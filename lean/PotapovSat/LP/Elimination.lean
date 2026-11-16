import PotapovSat.LP.Basic

/-!
# One step of the principal-hyperface method, and its correctness

A step of the method (G. G. Potapov, I. Yu. Grishin, 2007; I. Yu. Grishin, 2008)
takes a constraint `k`, replaces the inequality `A k ⬝ᵥ x ≤ b k` by the equality
`A k ⬝ᵥ x = b k`, solves it for a variable `x j` with `A k j ≠ 0`, and substitutes
the result into the objective and into all other constraints. The dimension drops
from `n + 1` to `n`. After `n` steps the chosen equalities form a triangular system,
and back substitution (`Problem.lift`) recovers the point in the original space.

## Main results

* `Problem.feasible_reduce_iff`: the reduced problem describes exactly the part of
  the original feasible set that lies on the hyperface `A k ⬝ᵥ x = b k`.
* `Problem.isOptimal_lift`: if `k` is a principal hyperface, back substitution of
  any optimum of the reduced problem is an optimum of the original problem.
* `Problem.not_isOptimal_lift`: if `k` is not principal, back substitution never
  yields an optimum, whatever happens afterwards.
* `PrincipalRun.isOptimal` and `Run.principal_of_isOptimal`: a full run of the
  method returns an optimal point **if and only if** every chosen hyperface is
  principal in the problem it was chosen from (`Run.isOptimal_iff`).
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Problem

variable {n : ℕ} {ι : Type*} (P : Problem K (n + 1) ι) (k : ι) (j : Fin (n + 1))

/-- The value of `x j` forced by `A k ⬝ᵥ x = b k` once the other coordinates are `y`. -/
def pivotValue (y : Fin n → K) : K :=
  (P.b k - ∑ l, P.A k (j.succAbove l) * y l) / P.A k j

/-- Back substitution: insert the forced value of `x j` into `y`. -/
def lift (y : Fin n → K) : Fin (n + 1) → K :=
  Fin.insertNth j (P.pivotValue k j y) y

/-- The problem obtained by eliminating `x j` with the equality `A k ⬝ᵥ x = b k`. -/
def reduce : Problem K n ι where
  c l := P.c (j.succAbove l) - P.c j * P.A k (j.succAbove l) / P.A k j
  A i l := P.A i (j.succAbove l) - P.A i j * P.A k (j.succAbove l) / P.A k j
  b i := P.b i - P.A i j * P.b k / P.A k j

/-- The constant lost from the objective by the substitution. -/
def objShift : K := P.c j * P.b k / P.A k j

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Substitution identity for an arbitrary linear form `u`. -/
theorem dot_lift (u : Fin (n + 1) → K) (y : Fin n → K) :
    u ⬝ᵥ P.lift k j y =
      (∑ l, (u (j.succAbove l) - u j * P.A k (j.succAbove l) / P.A k j) * y l)
        + u j * P.b k / P.A k j := by
  simp only [dotProduct, lift, pivotValue]
  rw [Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, sub_mul,
    Finset.sum_sub_distrib]
  have h : ∑ l, u j * P.A k (j.succAbove l) / P.A k j * y l
      = u j / P.A k j * ∑ l, P.A k (j.succAbove l) * y l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem A_dot_lift (i : ι) (y : Fin n → K) :
    P.A i ⬝ᵥ P.lift k j y = (P.reduce k j).A i ⬝ᵥ y + P.A i j * P.b k / P.A k j := by
  rw [P.dot_lift k j]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem obj_lift (y : Fin n → K) :
    P.obj (P.lift k j y) = (P.reduce k j).obj y + P.objShift k j := by
  rw [obj, P.dot_lift k j]
  rfl

/-- The reduced problem is exactly the original problem restricted to the hyperface. -/
theorem feasible_reduce_iff {y : Fin n → K} :
    (P.reduce k j).Feasible y ↔ P.Feasible (P.lift k j y) := by
  refine forall_congr' fun i => ?_
  rw [P.A_dot_lift k j i y]
  change _ ≤ P.b i - P.A i j * P.b k / P.A k j ↔ _
  constructor <;> intro h <;> linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Back substitution lands on the chosen hyperface. -/
theorem active_lift (hk : P.A k j ≠ 0) (y : Fin n → K) : P.Active k (P.lift k j y) := by
  unfold Active
  rw [P.dot_lift k j]
  have h0 : ∀ l, P.A k (j.succAbove l) - P.A k j * P.A k (j.succAbove l) / P.A k j = 0 :=
    fun l => by rw [mul_div_cancel_left₀ _ hk, sub_self]
  simp only [h0, zero_mul, Finset.sum_const_zero, zero_add]
  exact mul_div_cancel_left₀ _ hk

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every point of the hyperface is the back substitution of its remaining coordinates. -/
theorem lift_removeNth (hk : P.A k j ≠ 0) {x : Fin (n + 1) → K} (hx : P.Active k x) :
    P.lift k j (j.removeNth x) = x := by
  have hxj : P.pivotValue k j (j.removeNth x) = x j := by
    unfold Active dotProduct at hx
    rw [Fin.sum_univ_succAbove _ j] at hx
    unfold pivotValue
    rw [div_eq_iff hk]
    simp only [Fin.removeNth]
    linear_combination -hx
  unfold lift
  rw [hxj]
  exact Fin.insertNth_self_removeNth j x

/-- If the hyperface `k` is principal, the reduced problem has an optimum. -/
theorem exists_isOptimal_reduce (hk : P.A k j ≠ 0) (hp : P.IsPrincipal k) :
    ∃ y, (P.reduce k j).IsOptimal y := by
  obtain ⟨x, ⟨hxf, hxo⟩, hxa⟩ := hp
  have hlift := P.lift_removeNth k j hk hxa
  refine ⟨j.removeNth x, ?_, fun z hz => ?_⟩
  · rw [P.feasible_reduce_iff, hlift]
    exact hxf
  · have h1 := hxo _ ((P.feasible_reduce_iff k j).1 hz)
    rw [P.obj_lift, ← hlift, P.obj_lift] at h1
    linarith

/-- **Correctness of one step.** If the chosen hyperface is principal, back
substitution of an optimum of the reduced problem is an optimum of the original one. -/
theorem isOptimal_lift (hk : P.A k j ≠ 0) (hp : P.IsPrincipal k) {y : Fin n → K}
    (hy : (P.reduce k j).IsOptimal y) : P.IsOptimal (P.lift k j y) := by
  obtain ⟨x, ⟨hxf, hxo⟩, hxa⟩ := hp
  have hlift := P.lift_removeNth k j hk hxa
  refine ⟨(P.feasible_reduce_iff k j).1 hy.1, fun z hz => ?_⟩
  have hxr : (P.reduce k j).Feasible (j.removeNth x) := by
    rw [P.feasible_reduce_iff, hlift]
    exact hxf
  have h1 := hy.2 _ hxr
  have h2 : P.obj x = (P.reduce k j).obj (j.removeNth x) + P.objShift k j := by
    conv_lhs => rw [← hlift]
    exact P.obj_lift k j _
  rw [P.obj_lift]
  linarith [hxo z hz]

/-- An optimum obtained by back substitution comes from an optimum of the reduced
problem. -/
theorem isOptimal_reduce_of_isOptimal_lift {y : Fin n → K}
    (h : P.IsOptimal (P.lift k j y)) : (P.reduce k j).IsOptimal y := by
  refine ⟨(P.feasible_reduce_iff k j).2 h.1, fun z hz => ?_⟩
  have h1 := h.2 _ ((P.feasible_reduce_iff k j).1 hz)
  rw [P.obj_lift, P.obj_lift] at h1
  linarith

omit [IsStrictOrderedRing K] in
/-- An optimum obtained by back substitution proves the chosen hyperface principal. -/
theorem isPrincipal_of_isOptimal_lift (hk : P.A k j ≠ 0) {y : Fin n → K}
    (h : P.IsOptimal (P.lift k j y)) : P.IsPrincipal k :=
  ⟨_, h, P.active_lift k j hk y⟩

omit [IsStrictOrderedRing K] in
/-- **Failure of a non-principal choice.** If the chosen hyperface is not principal,
no continuation of the method can return an optimal point. -/
theorem not_isOptimal_lift (hk : P.A k j ≠ 0) (hnp : ¬ P.IsPrincipal k) (y : Fin n → K) :
    ¬ P.IsOptimal (P.lift k j y) :=
  fun h => hnp (P.isPrincipal_of_isOptimal_lift k j hk h)

/-- One step is correct exactly when the chosen hyperface is principal. -/
theorem isOptimal_lift_iff (hk : P.A k j ≠ 0) {y : Fin n → K}
    (hy : (P.reduce k j).IsOptimal y) :
    P.IsOptimal (P.lift k j y) ↔ P.IsPrincipal k :=
  ⟨P.isPrincipal_of_isOptimal_lift k j hk, fun hp => P.isOptimal_lift k j hk hp hy⟩

end Problem

/-! ## Full runs of the method -/

variable {ι : Type*}

/-- A run of the method on a problem with `n` variables, returning the point `x`:
`n` elimination steps with arbitrary (non-degenerate) pivot choices, then a feasible
point of the zero-dimensional problem. -/
inductive Run : {n : ℕ} → Problem K n ι → (Fin n → K) → Prop
  | base {P : Problem K 0 ι} {x : Fin 0 → K} : P.Feasible x → Run P x
  | step {n : ℕ} {P : Problem K (n + 1) ι} (k : ι) (j : Fin (n + 1)) (hk : P.A k j ≠ 0)
      {y : Fin n → K} : Run (P.reduce k j) y → Run P (P.lift k j y)

/-- A run in which every chosen hyperface is principal in the problem it is chosen from. -/
inductive PrincipalRun : {n : ℕ} → Problem K n ι → (Fin n → K) → Prop
  | base {P : Problem K 0 ι} {x : Fin 0 → K} : P.Feasible x → PrincipalRun P x
  | step {n : ℕ} {P : Problem K (n + 1) ι} (k : ι) (j : Fin (n + 1)) (hk : P.A k j ≠ 0)
      (hp : P.IsPrincipal k) {y : Fin n → K} :
      PrincipalRun (P.reduce k j) y → PrincipalRun P (P.lift k j y)

omit [IsStrictOrderedRing K] in
/-- In dimension zero every feasible point is optimal. -/
theorem Problem.isOptimal_of_dim_zero {P : Problem K 0 ι} {x : Fin 0 → K}
    (hx : P.Feasible x) : P.IsOptimal x :=
  ⟨hx, fun y _ => by rw [Subsingleton.elim y x]⟩

/-- **Soundness of the method.** If every chosen hyperface is principal, the method
returns an optimal point. -/
theorem PrincipalRun.isOptimal {n : ℕ} {P : Problem K n ι} {x : Fin n → K}
    (h : PrincipalRun P x) : P.IsOptimal x := by
  induction h with
  | base hx => exact Problem.isOptimal_of_dim_zero hx
  | step k j hk hp _ ih => exact Problem.isOptimal_lift _ k j hk hp ih

/-- **Completeness of the criterion.** If a run of the method returns an optimal point,
then every hyperface it chose was principal. -/
theorem Run.principal_of_isOptimal {n : ℕ} {P : Problem K n ι} {x : Fin n → K}
    (h : Run P x) (hopt : P.IsOptimal x) : PrincipalRun P x := by
  induction h with
  | base hx => exact .base hx
  | step k j hk _ ih =>
    exact .step k j hk (Problem.isPrincipal_of_isOptimal_lift _ k j hk hopt)
      (ih (Problem.isOptimal_reduce_of_isOptimal_lift _ k j hopt))

omit [IsStrictOrderedRing K] in
/-- A principal run is in particular a run. -/
theorem PrincipalRun.toRun {n : ℕ} {P : Problem K n ι} {x : Fin n → K}
    (h : PrincipalRun P x) : Run P x := by
  induction h with
  | base hx => exact .base hx
  | step k j hk _ _ ih => exact .step k j hk ih

/-- **Main theorem of the principal-hyperface method.** For any run of the method,
the returned point is optimal if and only if every chosen hyperface was principal. -/
theorem Run.isOptimal_iff {n : ℕ} {P : Problem K n ι} {x : Fin n → K} (h : Run P x) :
    P.IsOptimal x ↔ PrincipalRun P x :=
  ⟨h.principal_of_isOptimal, PrincipalRun.isOptimal⟩

end PotapovSat.LP
