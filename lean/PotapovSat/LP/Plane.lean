import PotapovSat.LP.Optimality
import PotapovSat.LP.Redundancy

/-!
# In the plane, the projection rule always selects a principal hyperface

For problems in two variables without redundant constraints, the constraint with the
largest projection of the objective vector onto its normal is active at **every**
optimal point. So in dimension 2 the selection rule of the principal-hyperface method
never errs. `PotapovSat.LP.ProjectionCounterexample` shows that this fails from
dimension 3 on.

## Proof idea

Write `p(v) = c ⬝ᵥ v` and `q(v) = c × v` (the 2D cross product). By the optimality
conditions, `c` is a non-negative combination of the active normals, so
`∑ yᵢ q(Aᵢ) = 0` and `∑ yᵢ p(Aᵢ) = ‖c‖² > 0`. The projection rule says that `A_k` makes a
strictly smaller angle with `c` than every active normal with positive projection. If
`q(A_k) ≥ 0`, some active normal `A_{i₂}` lies strictly on the same side of `c` and
beyond `A_k`. Then `A_k` is a non-negative combination of `c` and `A_{i₂}`, hence of
active normals. If `k` were not active, the cone obstruction
(`Problem.redundant_of_mem_activeCone`) would make `k` redundant. The case
`q(A_k) < 0` is symmetric.
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem dot_two (u v : Fin 2 → K) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

namespace Problem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Problem K 2 ι)

/-- **The projection rule is exact in the plane.** In a two-variable problem without
redundant constraints, the constraint with the largest projection of the objective
vector is active at every optimal point. -/
theorem active_of_isMaxProjection (hnr : ∀ i, ¬ P.Redundant i) {x : Fin 2 → K}
    (hx : P.IsOptimal x) {k : ι} (hk : P.IsMaxProjection k) : P.Active k x := by
  by_contra hka
  obtain ⟨y, hy0, hyact, hyc⟩ := P.exists_dual_of_isOptimal hx
  have hyk : y k = 0 := by
    by_contra h
    exact hka (hyact k h)
  obtain ⟨hpk, hmax⟩ := hk
  simp only [dot_two] at hpk hmax
  -- coordinates relative to `c`
  set c0 := P.c 0 with hc0
  set c1 := P.c 1 with hc1
  let p : ι → K := fun i => c0 * P.A i 0 + c1 * P.A i 1
  let q : ι → K := fun i => c0 * P.A i 1 - c1 * P.A i 0
  let N : ι → K := fun i => P.A i 0 * P.A i 0 + P.A i 1 * P.A i 1
  have hpk' : 0 < p k := hpk
  have hL : ∀ i, p i ^ 2 + q i ^ 2 = (c0 ^ 2 + c1 ^ 2) * N i := fun i => by
    simp only [p, q, N]
    ring
  have hc2 : 0 < c0 ^ 2 + c1 ^ 2 := by
    by_contra h
    have h0 : c0 = 0 := by nlinarith [sq_nonneg c0, sq_nonneg c1]
    have h1 : c1 = 0 := by nlinarith [sq_nonneg c0, sq_nonneg c1]
    simp only [p, h0, h1] at hpk'
    simp at hpk'
  have hy0' : ∑ i, y i * P.A i 0 = c0 := hyc 0
  have hy1' : ∑ i, y i * P.A i 1 = c1 := hyc 1
  have hsp : ∑ i, y i * p i = c0 ^ 2 + c1 ^ 2 := by
    have e : ∀ i, y i * p i = c0 * (y i * P.A i 0) + c1 * (y i * P.A i 1) := fun i => by
      simp only [p]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hy0', hy1']
    ring
  have hsq : ∑ i, y i * q i = 0 := by
    have e : ∀ i, y i * q i = c0 * (y i * P.A i 1) - c1 * (y i * P.A i 0) := fun i => by
      simp only [q]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hy0', hy1']
    ring
  -- the projection rule in `(p, q)` coordinates
  have hproj : ∀ i, i ≠ k → 0 < p i → p i ^ 2 * q k ^ 2 < p k ^ 2 * q i ^ 2 := by
    intro i hi hpi
    have hm : p i ^ 2 * N k < p k ^ 2 * N i := hmax i hi hpi
    have hm' := mul_lt_mul_of_pos_left hm hc2
    calc p i ^ 2 * q k ^ 2 = p i ^ 2 * (p k ^ 2 + q k ^ 2) - p i ^ 2 * p k ^ 2 := by ring
      _ = (c0 ^ 2 + c1 ^ 2) * (p i ^ 2 * N k) - p i ^ 2 * p k ^ 2 := by rw [hL k]; ring
      _ < (c0 ^ 2 + c1 ^ 2) * (p k ^ 2 * N i) - p i ^ 2 * p k ^ 2 := by linarith
      _ = p k ^ 2 * (p i ^ 2 + q i ^ 2) - p i ^ 2 * p k ^ 2 := by rw [hL i]; ring
      _ = p k ^ 2 * q i ^ 2 := by ring
  -- an active normal with positive projection exists
  have hexp : ∃ i, y i ≠ 0 ∧ 0 < p i := by
    have h : ∑ _i : ι, (0 : K) < ∑ i, y i * p i := by simp [hsp, hc2]
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt h
    refine ⟨i, fun h0 => by simp [h0] at hi, ?_⟩
    by_contra hle
    push Not at hle
    nlinarith [hy0 i]
  -- final step: `A k` is a non-negative combination of `c` and an active `A i₂`
  have finish : ∀ i₂, y i₂ ≠ 0 → q i₂ ≠ 0 →
      0 ≤ (P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0) / q i₂ → 0 ≤ q k / q i₂ → False := by
    intro i₂ hy2 hq2 hα hβ
    have hk2 : k ≠ i₂ := fun h => hka (h ▸ hyact i₂ hy2)
    apply hnr k
    refine P.redundant_of_mem_activeCone k
      (fun i => (P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0) / q i₂ * y i +
        if i = i₂ then q k / q i₂ else 0)
      (fun i => ?_) ?_ (fun j => ?_) hx.1 (fun i hi => ?_)
    · have := hy0 i
      split_ifs
      · positivity
      · simpa using mul_nonneg hα this
    · simp [hyk, hk2]
    · have hsum : ∑ i, ((P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0) / q i₂ * y i +
          (if i = i₂ then q k / q i₂ else 0)) * P.A i j
          = (P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0) / q i₂ * P.c j +
            q k / q i₂ * P.A i₂ j := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hyc j,
          ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hid : ∀ j : Fin 2, (P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0) * P.c j +
          q k * P.A i₂ j = P.A k j * q i₂ := by
        intro j
        fin_cases j <;> simp [q, hc0, hc1] <;> ring
      rw [hsum, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hq2, hid j]
    · by_cases hy : y i = 0
      · by_cases h : i = i₂
        · exact h ▸ hyact i₂ hy2
        · simp [hy, h] at hi
      · exact hyact i hy
  have hs : ∀ i, (c0 ^ 2 + c1 ^ 2) * (P.A k 0 * P.A i 1 - P.A k 1 * P.A i 0)
      = p k * q i - q k * p i := fun i => by
    simp only [p, q]
    ring
  rcases le_or_gt 0 (q k) with hqk | hqk
  · -- `A k` lies on the non-negative side of `c`
    have : ∃ i₂, y i₂ ≠ 0 ∧ 0 < q i₂ := by
      by_contra hno
      push Not at hno
      have hterm : ∀ i ∈ Finset.univ, y i * q i ≤ 0 := fun i _ => by
        by_cases h : y i = 0
        · simp [h]
        · nlinarith [hy0 i, hno i h]
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsq
      obtain ⟨i, hyi, hpi⟩ := hexp
      have hqi : q i = 0 := by
        rcases mul_eq_zero.1 (hzero i (Finset.mem_univ i)) with h | h
        · exact absurd h hyi
        · exact h
      have hik : i ≠ k := fun h => hyi (h ▸ hyk)
      have := hproj i hik hpi
      rw [hqi] at this
      nlinarith [sq_nonneg (p i), sq_nonneg (q k)]
    obtain ⟨i₂, hy2, hq2⟩ := this
    have hs2 : 0 < p k * q i₂ - q k * p i₂ := by
      rcases le_or_gt (p i₂) 0 with hp2 | hp2
      · nlinarith
      · have hi2k : i₂ ≠ k := fun h => hy2 (h ▸ hyk)
        have := hproj i₂ hi2k hp2
        have hlt : p i₂ * q k < p k * q i₂ :=
          lt_of_pow_lt_pow_left₀ 2 (by positivity) (by rw [mul_pow, mul_pow]; linarith)
        linarith
    have hs2' : 0 < P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0 := by
      have := hs i₂
      nlinarith
    exact finish i₂ hy2 hq2.ne' (div_nonneg hs2'.le hq2.le) (div_nonneg hqk hq2.le)
  · -- `A k` lies on the negative side of `c`
    have : ∃ i₂, y i₂ ≠ 0 ∧ q i₂ < 0 := by
      by_contra hno
      push Not at hno
      have hterm : ∀ i ∈ Finset.univ, 0 ≤ y i * q i := fun i _ => by
        by_cases h : y i = 0
        · simp [h]
        · exact mul_nonneg (hy0 i) (hno i h)
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsq
      obtain ⟨i, hyi, hpi⟩ := hexp
      have hqi : q i = 0 := by
        rcases mul_eq_zero.1 (hzero i (Finset.mem_univ i)) with h | h
        · exact absurd h hyi
        · exact h
      have hik : i ≠ k := fun h => hyi (h ▸ hyk)
      have := hproj i hik hpi
      rw [hqi] at this
      have hnn : (0 : K) ≤ p i ^ 2 * q k ^ 2 := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
      linarith
    obtain ⟨i₂, hy2, hq2⟩ := this
    have hs2 : p k * q i₂ - q k * p i₂ < 0 := by
      rcases le_or_gt (p i₂) 0 with hp2 | hp2
      · have h1 : p k * q i₂ < 0 := mul_neg_of_pos_of_neg hpk' hq2
        have h2 : 0 ≤ q k * p i₂ := mul_nonneg_of_nonpos_of_nonpos hqk.le hp2
        linarith
      · have hi2k : i₂ ≠ k := fun h => hy2 (h ▸ hyk)
        have := hproj i₂ hi2k hp2
        have hlt : p i₂ * (-q k) < p k * (-q i₂) :=
          lt_of_pow_lt_pow_left₀ 2 (mul_pos hpk' (neg_pos.2 hq2)).le
            (by rw [mul_pow, mul_pow, neg_sq, neg_sq]; linarith)
        linarith
    have hs2' : P.A k 0 * P.A i₂ 1 - P.A k 1 * P.A i₂ 0 < 0 := by
      by_contra h
      push Not at h
      have := mul_nonneg hc2.le h
      linarith [hs i₂]
    exact finish i₂ hy2 hq2.ne (div_nonneg_of_nonpos hs2'.le hq2.le)
      (div_nonneg_of_nonpos hqk.le hq2.le)

/-- **Corollary.** In a two-variable problem without redundant constraints that has an
optimum, the constraint selected by the projection rule is a principal hyperface. -/
theorem isPrincipal_of_isMaxProjection (hnr : ∀ i, ¬ P.Redundant i) {x : Fin 2 → K}
    (hx : P.IsOptimal x) {k : ι} (hk : P.IsMaxProjection k) : P.IsPrincipal k :=
  ⟨x, hx, P.active_of_isMaxProjection hnr hx hk⟩

end Problem

end PotapovSat.LP
