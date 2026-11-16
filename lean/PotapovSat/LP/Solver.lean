import PotapovSat.LP.Elimination
import PotapovSat.LP.Optimality

/-!
# The certified principal-hyperface method with backtracking

This file turns the method of principal hyperfaces into an algorithm that is proved to
return an optimal point whenever one exists.

At each level the algorithm

1. orders the constraints by the selection rule of the method: largest projection
   `(c ⬝ᵥ A k) / ‖A k‖` first;
2. for each constraint in this order, picks the pivot variable with the largest
   coefficient in absolute value (as in Grishin, 2008), eliminates it, and solves the
   reduced problem recursively;
3. assembles a dual certificate for the current problem from the certificate of the
   reduced problem. If the certificate checks, the answer is **certified optimal** and
   the algorithm stops at once;
4. otherwise it *repairs* the choice by backtracking to the next constraint. If no
   choice is certified, it returns the best feasible candidate found.

Main results:

* `Problem.solve_feasible`: every returned point is feasible.
* `Problem.solve_isOptimal`: if the problem has an optimal point, the algorithm returns
  one. Termination is structural (recursion on the dimension, finitely many candidates
  per level). Completeness rests on `Problem.exists_isPrincipal`: a principal hyperface
  always exists, so the search always contains a correct branch.
* `Problem.Certified.isOptimal`: a certified answer is optimal, independently of how it
  was found.

No polynomial bound on the running time is proved: a call with `n ≥ 1` variables and `m`
constraints makes at most `2m` recursive calls. `PotapovSat.LP.Examples.SolverDemo` shows
the results on two examples.
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m : ℕ}

namespace Problem

variable {n : ℕ}

instance decFeasible (P : Problem K n (Fin m)) : DecidablePred P.Feasible :=
  fun x => inferInstanceAs (Decidable (∀ i, P.A i ⬝ᵥ x ≤ P.b i))

/-- `z` is a dual certificate proving that `x` is optimal. -/
def Certified (P : Problem K n (Fin m)) (x : Fin n → K) (z : Fin m → K) : Prop :=
  P.Feasible x ∧ (∀ i, 0 ≤ z i) ∧ (∀ j, ∑ i, z i * P.A i j = P.c j) ∧
    P.obj x = ∑ i, z i * P.b i

instance (P : Problem K n (Fin m)) (x : Fin n → K) (z : Fin m → K) :
    Decidable (P.Certified x z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A certified answer is optimal. -/
theorem Certified.isOptimal {P : Problem K n (Fin m)} {x : Fin n → K} {z : Fin m → K}
    (h : P.Certified x z) : P.IsOptimal x :=
  P.isOptimal_of_certificate h.1 z h.2.1 h.2.2.1 h.2.2.2

/-- Score used by the selection rule: the squared projection for constraints with a
positive projection, and `-1` otherwise. -/
def score (P : Problem K n (Fin m)) (k : Fin m) : K :=
  if 0 < P.c ⬝ᵥ P.A k then (P.c ⬝ᵥ P.A k) ^ 2 / (P.A k ⬝ᵥ P.A k) else -1

/-- Constraints in the order of the selection rule (largest projection first). -/
def order (P : Problem K n (Fin m)) : List (Fin m) :=
  (List.finRange m).mergeSort fun a b => decide (P.score b ≤ P.score a)

theorem mem_order (P : Problem K n (Fin m)) (k : Fin m) : k ∈ P.order := by
  simp [order, List.mem_finRange]

/-- Pivot variable for constraint `k`: the largest coefficient in absolute value, if it
is non-zero. -/
def pivot (P : Problem K (n + 1) (Fin m)) (k : Fin m) : Option (Fin (n + 1)) :=
  ((List.finRange (n + 1)).argmax fun j => |P.A k j|).filter fun j => decide (P.A k j ≠ 0)

theorem pivot_ne_zero {P : Problem K (n + 1) (Fin m)} {k : Fin m} {j : Fin (n + 1)}
    (h : P.pivot k = some j) : P.A k j ≠ 0 := by
  simp only [pivot, Option.filter_eq_some_iff, decide_eq_true_eq] at h
  exact h.2

theorem exists_pivot {P : Problem K (n + 1) (Fin m)} {k : Fin m} {j₀ : Fin (n + 1)}
    (h : P.A k j₀ ≠ 0) : ∃ j, P.pivot k = some j := by
  have hne : (List.finRange (n + 1)).argmax (fun j => |P.A k j|) ≠ none := by
    rw [ne_eq, List.argmax_eq_none]
    exact List.ne_nil_of_mem (List.mem_finRange j₀)
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hne
  have hle : |P.A k j₀| ≤ |P.A k j| := List.le_of_mem_argmax (f := fun j => |P.A k j|) (List.mem_finRange j₀) hj
  have hj0 : P.A k j ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hle
    exact h (abs_nonpos_iff.1 hle)
  exact ⟨j, by simp [pivot, hj, hj0]⟩

/-- The same problem with its data stored in arrays. Mathematically `P.memo = P`
(`memo_eq`); computationally it stops nested eliminations from re-evaluating entries. -/
def memo (P : Problem K n (Fin m)) : Problem K n (Fin m) :=
  let c := Vector.ofFn P.c
  let A := Vector.ofFn fun i => Vector.ofFn (P.A i)
  let b := Vector.ofFn P.b
  ⟨fun j => c.get j, fun i j => (A.get i).get j, fun i => b.get i⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem memo_eq (P : Problem K n (Fin m)) : P.memo = P := by
  cases P
  simp [memo]

/-- Dual multipliers for the current problem, assembled from those of the problem
reduced by `k` and `j`. -/
def composeDual (P : Problem K (n + 1) (Fin m)) (k : Fin m) (j : Fin (n + 1))
    (z' : Fin m → K) : Fin m → K :=
  fun i => if i = k then
      (P.c j - ∑ i', (if i' = k then 0 else z' i') * P.A i' j) / P.A k j
    else z' i

/-- One branch of the search: eliminate with constraint `k`, solve the reduced problem
with `rec`, and lift the answer back. -/
def stepWith (rec : Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K)))
    (P : Problem K (n + 1) (Fin m)) (k : Fin m) :
    Option ((Fin (n + 1) → K) × (Fin m → K)) :=
  match P.pivot k with
  | none => none
  | some j => (rec (P.reduce k j).memo).map fun r => (P.lift k j r.1, P.composeDual k j r.2)

/-- All candidates of one level: the origin (if feasible) and every branch. -/
def candidates (rec : Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K)))
    (P : Problem K (n + 1) (Fin m)) : List ((Fin (n + 1) → K) × (Fin m → K)) :=
  (if P.Feasible 0 then [(0, 0)] else []) ++ P.order.filterMap (stepWith rec P)

/-- One level of the method: the first certified branch in the order of the selection
rule; if there is none, the best candidate. -/
def solveWith (rec : Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K)))
    (P : Problem K (n + 1) (Fin m)) : Option ((Fin (n + 1) → K) × (Fin m → K)) :=
  match P.order.findSome? (fun k =>
      (stepWith rec P k).filter fun r => decide (P.Certified r.1 r.2)) with
  | some r => some r
  | none => (candidates rec P).argmax fun r => P.obj r.1

/-- **The certified principal-hyperface method.** Returns a point together with
candidate dual multipliers. -/
def solve : {n : ℕ} → Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K))
  | 0, P => if P.Feasible 0 then some (0, 0) else none
  | _ + 1, P => solveWith (fun Q => solve Q) P

/-! ## Soundness: every answer is feasible -/

section Soundness

variable (rec : Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K)))
  (hrec : ∀ Q r, rec Q = some r → Q.Feasible r.1)
include hrec

theorem feasible_of_stepWith {P : Problem K (n + 1) (Fin m)} {k : Fin m}
    {r : (Fin (n + 1) → K) × (Fin m → K)} (h : stepWith rec P k = some r) :
    P.Feasible r.1 := by
  unfold stepWith at h
  split at h
  · simp at h
  · rename_i j _
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
    rw [memo_eq] at hr'
    exact (P.feasible_reduce_iff k j).1 (hrec _ _ hr')

theorem feasible_of_mem_candidates {P : Problem K (n + 1) (Fin m)}
    {r : (Fin (n + 1) → K) × (Fin m → K)} (h : r ∈ candidates rec P) : P.Feasible r.1 := by
  unfold candidates at h
  rcases List.mem_append.1 h with h | h
  · split_ifs at h with h0
    · simp only [List.mem_singleton] at h
      subst h
      exact h0
    · simp at h
  · obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 h
    exact feasible_of_stepWith rec hrec hk

theorem feasible_of_solveWith {P : Problem K (n + 1) (Fin m)}
    {r : (Fin (n + 1) → K) × (Fin m → K)} (h : solveWith rec P = some r) :
    P.Feasible r.1 := by
  unfold solveWith at h
  split at h
  · rename_i r' hr'
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some hr'
    rw [Option.filter_eq_some_iff] at hk
    cases h
    exact (of_decide_eq_true hk.2).1
  · exact feasible_of_mem_candidates rec hrec (List.argmax_mem h)

end Soundness

/-- **Soundness.** Every point returned by the method is feasible. -/
theorem solve_feasible : ∀ {n : ℕ} (P : Problem K n (Fin m)) (r : (Fin n → K) × (Fin m → K)),
    P.solve = some r → P.Feasible r.1
  | 0, P, r, h => by
    simp only [solve] at h
    split_ifs at h with h0
    cases h
    exact h0
  | _ + 1, P, r, h => feasible_of_solveWith _ (fun Q r hr => solve_feasible Q r hr) h

/-! ## Completeness: an optimum is always found -/

/-- With a zero objective and a non-zero constraint row, some constraint with a non-zero
coefficient is active at some feasible point: move from a feasible point along a
constraint normal until the first constraint becomes tight. -/
theorem exists_active_of_ne_zero (P : Problem K n (Fin m)) {x : Fin n → K}
    (hx : P.Feasible x) {k₀ : Fin m} {j₀ : Fin n} (h : P.A k₀ j₀ ≠ 0) :
    ∃ x' k j, P.Feasible x' ∧ P.Active k x' ∧ P.A k j ≠ 0 := by
  set d := P.A k₀ with hd
  have hdd : 0 < d ⬝ᵥ d := by
    have h1 : 0 ≤ d ⬝ᵥ d := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : d ⬝ᵥ d ≠ 0 := fun h0 => h (congrFun (dotProduct_self_eq_zero.1 h0) j₀)
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  set R := Finset.univ.filter (fun r => 0 < P.A r ⬝ᵥ d) with hR_def
  have hR : R.Nonempty := ⟨k₀, by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdd⟩
  set t : Fin m → K := fun r => (P.b r - P.A r ⬝ᵥ x) / (P.A r ⬝ᵥ d) with ht_def
  obtain ⟨r, hrR, hmin⟩ := R.exists_min_image t hR
  have hrpos : 0 < P.A r ⬝ᵥ d := by simpa [R] using hrR
  have ht0 : 0 ≤ t r := div_nonneg (sub_nonneg.2 (hx r)) hrpos.le
  have hj : ∃ j, P.A r j ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : P.A r = 0 := funext hall
    rw [h0, zero_dotProduct] at hrpos
    exact lt_irrefl _ hrpos
  obtain ⟨j, hj⟩ := hj
  refine ⟨x + t r • d, r, j, ?_, ?_, hj⟩
  · intro i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hi : 0 < P.A i ⬝ᵥ d
    · have hle : t r ≤ t i := hmin i (by simp [R, hi])
      have h1 : t r * (P.A i ⬝ᵥ d) ≤ t i * (P.A i ⬝ᵥ d) := mul_le_mul_of_nonneg_right hle hi.le
      have h2 : t i * (P.A i ⬝ᵥ d) = P.b i - P.A i ⬝ᵥ x := div_mul_cancel₀ _ hi.ne'
      linarith
    · push Not at hi
      have h1 : t r * (P.A i ⬝ᵥ d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hi
      linarith [hx i]
  · unfold Active
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h1 : t r * (P.A r ⬝ᵥ d) = P.b r - P.A r ⬝ᵥ x := div_mul_cancel₀ _ hrpos.ne'
    linarith

/-- If a problem has an optimum, then either some principal hyperface has a non-zero
coefficient, or every constraint row is zero and the origin is optimal. -/
theorem exists_isPrincipal_or_zero (P : Problem K n (Fin m)) {x : Fin n → K}
    (hx : P.IsOptimal x) :
    (∃ k j, P.IsPrincipal k ∧ P.A k j ≠ 0) ∨ P.IsOptimal 0 := by
  by_cases hrows : ∀ k j, P.A k j = 0
  · right
    obtain ⟨y, -, -, hyc⟩ := P.exists_dual_of_isOptimal hx
    have hc : P.c = 0 := funext fun j => by rw [← hyc j]; simp [hrows]
    refine ⟨fun i => ?_, fun z _ => by simp [obj, hc]⟩
    have := hx.1 i
    have hA : P.A i = 0 := funext (hrows i)
    simpa [hA] using this
  · left
    push Not at hrows
    obtain ⟨k₀, j₀, h₀⟩ := hrows
    by_cases hc : P.c = 0
    · obtain ⟨x', k, j, hx', hk, hkj⟩ := P.exists_active_of_ne_zero hx.1 h₀
      exact ⟨k, j, ⟨x', ⟨hx', fun z _ => by simp [obj, hc]⟩, hk⟩, hkj⟩
    · exact P.exists_isPrincipal hx hc

section Completeness

variable (rec : Problem K n (Fin m) → Option ((Fin n → K) × (Fin m → K)))
  (hrec : ∀ Q r, rec Q = some r → Q.Feasible r.1)
  (hopt : ∀ Q : Problem K n (Fin m), (∃ x, Q.IsOptimal x) →
    ∃ r, rec Q = some r ∧ Q.IsOptimal r.1)
include hrec hopt

omit hrec in
/-- Some candidate of a level is optimal. -/
theorem exists_optimal_candidate {P : Problem K (n + 1) (Fin m)} {x : Fin (n + 1) → K}
    (hx : P.IsOptimal x) : ∃ r ∈ candidates rec P, P.IsOptimal r.1 := by
  rcases P.exists_isPrincipal_or_zero hx with ⟨k, j₀, hk, hkj₀⟩ | h0
  · obtain ⟨j, hj⟩ := exists_pivot hkj₀
    have hkj := pivot_ne_zero hj
    obtain ⟨y, hy⟩ := P.exists_isOptimal_reduce k j hkj hk
    obtain ⟨r', hr', hr'opt⟩ := hopt _ ⟨y, hy⟩
    refine ⟨(P.lift k j r'.1, P.composeDual k j r'.2), ?_, P.isOptimal_lift k j hkj hk hr'opt⟩
    unfold candidates
    refine List.mem_append_right _ (List.mem_filterMap.2 ⟨k, P.mem_order k, ?_⟩)
    simp [stepWith, hj, hr']
  · refine ⟨(0, 0), ?_, h0⟩
    unfold candidates
    simp [h0.1]

theorem isOptimal_of_solveWith {P : Problem K (n + 1) (Fin m)} {x : Fin (n + 1) → K}
    (hx : P.IsOptimal x) : ∃ r, solveWith rec P = some r ∧ P.IsOptimal r.1 := by
  unfold solveWith
  split
  · rename_i r' hr'
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some hr'
    rw [Option.filter_eq_some_iff] at hk
    exact ⟨r', rfl, (of_decide_eq_true hk.2).isOptimal⟩
  · obtain ⟨r₀, hr₀, hr₀opt⟩ := exists_optimal_candidate rec hopt hx
    have hne : (candidates rec P).argmax (fun r => P.obj r.1) ≠ none := by
      rw [ne_eq, List.argmax_eq_none]
      exact List.ne_nil_of_mem hr₀
    obtain ⟨best, hbest⟩ := Option.ne_none_iff_exists'.1 hne
    have hbf := feasible_of_mem_candidates rec hrec (List.argmax_mem hbest)
    have hle : P.obj r₀.1 ≤ P.obj best.1 := List.le_of_mem_argmax (f := fun r => P.obj r.1) hr₀ hbest
    exact ⟨best, hbest, hbf, fun z hz => le_trans (hr₀opt.2 z hz) hle⟩

end Completeness

/-- **Completeness and correctness of the certified method.** If the problem has an
optimal point, the method returns an optimal point. -/
theorem solve_isOptimal : ∀ {n : ℕ} (P : Problem K n (Fin m)), (∃ x, P.IsOptimal x) →
    ∃ r, P.solve = some r ∧ P.IsOptimal r.1
  | 0, P, ⟨x, hx⟩ => by
    have hx0 : x = 0 := Subsingleton.elim _ _
    subst hx0
    refine ⟨(0, 0), ?_, hx⟩
    show (if P.Feasible 0 then some (0, 0) else none) = some (0, 0)
    rw [ite_eq_left hx.1]
  | _ + 1, P, ⟨_, hx⟩ =>
    isOptimal_of_solveWith _ (fun Q r hr => solve_feasible Q r hr)
      (fun Q hQ => solve_isOptimal Q hQ) hx

/-- If the problem has an optimum, the value found by the method is the optimal value. -/
theorem solve_obj_eq {P : Problem K n (Fin m)} {x : Fin n → K} (hx : P.IsOptimal x) :
    ∃ r, P.solve = some r ∧ P.obj r.1 = P.obj x := by
  obtain ⟨r, hr, hropt⟩ := P.solve_isOptimal ⟨x, hx⟩
  exact ⟨r, hr, le_antisymm (hx.2 _ hropt.1) (hropt.2 _ hx.1)⟩

end Problem

end PotapovSat.LP
