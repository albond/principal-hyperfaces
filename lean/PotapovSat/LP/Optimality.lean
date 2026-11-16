import PotapovSat.LP.Farkas

/-!
# Optimality conditions and existence of principal hyperfaces

From Farkas' lemma we derive the optimality theorem for linear programs:

* `Problem.exists_dual_of_isOptimal` (Karush–Kuhn–Tucker conditions): at an optimal
  point, the objective vector is a non-negative combination of the normals of the active
  constraints.
* `Problem.isOptimal_iff_exists_certificate` (strong duality at an optimum): a feasible
  point is optimal if and only if a dual certificate of equal value exists. So every
  optimum can be verified independently.
* `Problem.exists_principal`: if the objective is non-zero, every optimal point lies on a
  principal hyperface with a non-zero pivot coefficient. This is the foundation of the
  principal-hyperface method: the object it searches for always exists.
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A small enough positive step respects every slack: if `s ≥ 0` and `u i ≤ 0` wherever
`s i = 0`, then `ε * u i ≤ s i` for some `ε > 0` and all `i`. -/
theorem exists_pos_step {ι : Type*} [Fintype ι] (u s : ι → K) (hs : ∀ i, 0 ≤ s i)
    (hu : ∀ i, s i = 0 → u i ≤ 0) : ∃ ε : K, 0 < ε ∧ ∀ i, ε * u i ≤ s i := by
  classical
  set r : ι → K := fun i => if s i = 0 then 0 else |u i| / s i with hr_def
  have hr : ∀ i, 0 ≤ r i := fun i => by
    simp only [hr_def]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (abs_nonneg _) (hs i)
  set R : K := ∑ i, r i with hR_def
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => hr i
  have hpos : (0 : K) < 1 / (1 + R) := by positivity
  refine ⟨1 / (1 + R), hpos, fun i => ?_⟩
  by_cases h0 : s i = 0
  · rw [h0]
    nlinarith [hu i h0]
  · have hspos : 0 < s i := lt_of_le_of_ne (hs i) (Ne.symm h0)
    have hri : r i = |u i| / s i := by simp [hr_def, h0]
    have hriR : r i ≤ R := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
    have habs : |u i| = r i * s i := by rw [hri, div_mul_cancel₀ _ h0]
    calc 1 / (1 + R) * u i ≤ 1 / (1 + R) * |u i| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hpos.le
      _ = r i / (1 + R) * s i := by rw [habs]; ring
      _ ≤ 1 * s i := by
          refine mul_le_mul_of_nonneg_right ?_ hspos.le
          rw [div_le_one (by positivity)]
          linarith
      _ = s i := one_mul _

namespace Problem

variable {n : ℕ} {ι : Type*} [Fintype ι] (P : Problem K n ι)

/-- **Optimality conditions.** At an optimal point, the objective vector is a non-negative
combination of the normals of the constraints active there. -/
theorem exists_dual_of_isOptimal [DecidableEq ι] {x : Fin n → K} (hx : P.IsOptimal x) :
    ∃ y : ι → K, (∀ i, 0 ≤ y i) ∧ (∀ i, y i ≠ 0 → P.Active i x) ∧
      ∀ j, ∑ i, y i * P.A i j = P.c j := by
  classical
  let A' : Option ι → Fin n → K :=
    fun o => o.elim (-P.c) (fun i => if P.Active i x then P.A i else 0)
  let b' : Option ι → K := fun o => o.elim (-1) (fun _ => 0)
  rcases farkas n A' b' with ⟨d, hd⟩ | ⟨y', hy0, hyA, hyb⟩
  · exfalso
    have hcd : 1 ≤ P.c ⬝ᵥ d := by
      have := hd none
      simp only [A', b', Option.elim_none, neg_dotProduct] at this
      linarith
    have hact : ∀ i, P.Active i x → P.A i ⬝ᵥ d ≤ 0 := fun i hi => by
      have := hd (some i)
      simpa [A', b', hi] using this
    obtain ⟨ε, hε, hstep⟩ := exists_pos_step (fun i => P.A i ⬝ᵥ d)
      (fun i => P.b i - P.A i ⬝ᵥ x) (fun i => sub_nonneg.2 (hx.1 i))
      (fun i hi => hact i (by unfold Active; linarith [hx.1 i]))
    have hfeas : P.Feasible (x + ε • d) := fun i => by
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith [hstep i]
    have hle := hx.2 _ hfeas
    simp only [obj, dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
    nlinarith
  · have hbn : 0 < y' none := by
      rw [Fintype.sum_option] at hyb
      simp only [b', Option.elim_none, Option.elim_some, mul_zero, Finset.sum_const_zero,
        add_zero] at hyb
      linarith
    refine ⟨fun i => (if P.Active i x then y' (some i) else 0) / y' none, fun i => ?_,
      fun i hi => ?_, fun j => ?_⟩
    · dsimp only
      split_ifs
      · exact div_nonneg (hy0 _) hbn.le
      · simp
    · by_contra h
      simp [h] at hi
    · have h1 := hyA j
      rw [Fintype.sum_option] at h1
      simp only [A', Option.elim_none, Option.elim_some, Pi.neg_apply] at h1
      have h1' : ∑ i, y' (some i) * (if P.Active i x then P.A i else 0) j
          = y' none * P.c j := by linarith
      have h2 : ∑ i, (if P.Active i x then y' (some i) else 0) / y' none * P.A i j
          = (∑ i, y' (some i) * (if P.Active i x then P.A i else 0) j) / y' none := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp [div_mul_eq_mul_div]
      rw [h2, h1']
      field_simp

/-- At an optimum, the dual certificate from the optimality conditions has the same value
as the optimum (strong duality). -/
theorem exists_certificate_of_isOptimal [DecidableEq ι] {x : Fin n → K}
    (hx : P.IsOptimal x) :
    ∃ y : ι → K, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * P.A i j = P.c j) ∧
      P.obj x = ∑ i, y i * P.b i := by
  obtain ⟨y, hy0, hyact, hyc⟩ := P.exists_dual_of_isOptimal hx
  refine ⟨y, hy0, hyc, ?_⟩
  rw [obj, P.comb_dot y P.c hyc x]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : y i = 0
  · simp [h]
  · rw [hyact i h]

/-- **Strong duality at an optimum.** A feasible point is optimal if and only if a dual
certificate of the same value exists. -/
theorem isOptimal_iff_exists_certificate [DecidableEq ι] {x : Fin n → K}
    (hx : P.Feasible x) :
    P.IsOptimal x ↔ ∃ y : ι → K, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * P.A i j = P.c j) ∧
      P.obj x = ∑ i, y i * P.b i :=
  ⟨P.exists_certificate_of_isOptimal, fun ⟨y, hy0, hyc, hval⟩ =>
    P.isOptimal_of_certificate hx y hy0 hyc hval⟩

/-- **Principal hyperfaces exist.** If the objective is non-zero, every optimal point lies
on some constraint hyperface whose normal has a non-zero coefficient, so the method can
always take a correct, non-degenerate step. -/
theorem exists_principal [DecidableEq ι] {x : Fin n → K} (hx : P.IsOptimal x)
    (hc : P.c ≠ 0) : ∃ k j, P.Active k x ∧ P.A k j ≠ 0 := by
  obtain ⟨y, -, hyact, hyc⟩ := P.exists_dual_of_isOptimal hx
  by_contra h
  push Not at h
  apply hc
  funext j
  rw [← hyc j, Pi.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hy : y i = 0
  · simp [hy]
  · rw [h i j (hyact i hy), mul_zero]

/-- Consequently, some constraint is a principal hyperface with a usable pivot. -/
theorem exists_isPrincipal [DecidableEq ι] {x : Fin n → K} (hx : P.IsOptimal x)
    (hc : P.c ≠ 0) : ∃ k j, P.IsPrincipal k ∧ P.A k j ≠ 0 := by
  obtain ⟨k, j, hk, hkj⟩ := P.exists_principal hx hc
  exact ⟨k, j, ⟨x, hx, hk⟩, hkj⟩

end Problem

end PotapovSat.LP
