import PotapovSat.LP.Elimination
import PotapovSat.LP.Redundancy

/-!
# The projection rule alone does not always pick a principal hyperface

The method of principal hyperfaces selects the constraint with the largest projection
`(c ⬝ᵥ A k) / ‖A k‖` of the objective vector onto its normal. Grishin (2008) notes that
the heuristic may, "with a certain probability", select a non-optimal face. This file
gives an explicit, machine-checked instance in dimension 3, for a bounded problem
without redundant constraints:

  maximize `z` subject to

  L1: `x + z ≤ 0`
  L2: `−x + y + z ≤ 0`
  L3: `−x − y + z ≤ 0`
  L4: `7y + 10z ≤ 1`
  L5: `−z ≤ 10`

The unique optimum is the origin, where L1, L2, L3 are active. L4 has the largest
projection (`10 / √149 ≈ 0.819`, against `1 / √2 ≈ 0.707` for L1), but it is not
active at the optimum. By `Problem.not_isOptimal_lift`, any run of the method that
starts with L4 returns a non-optimal point.

The normal of L4 lies outside the cone spanned by the active normals L1, L2, L3. By
`Problem.not_mem_activeCone`, this is the only way a non-redundant constraint with a
better projection can coexist with the true optimum.
-/

namespace PotapovSat.LP.ProjectionCounterexample

open Problem

/-- The counterexample. Constraint `Lm` has index `m - 1`. -/
def P : Problem ℚ 3 (Fin 5) where
  c := ![0, 0, 1]
  A := ![![1, 0, 1], ![-1, 1, 1], ![-1, -1, 1], ![0, 7, 10], ![0, 0, -1]]
  b := ![0, 0, 0, 1, 10]

theorem origin_feasible : P.Feasible 0 := by
  intro i
  fin_cases i <;> simp [P]

/-- The origin is optimal, with dual certificate `(1/2, 1/4, 1/4, 0, 0)`. -/
theorem origin_isOptimal : P.IsOptimal 0 :=
  P.isOptimal_of_certificate origin_feasible ![1/2, 1/4, 1/4, 0, 0]
    (fun i => by fin_cases i <;> simp)
    (fun j => by fin_cases j <;> simp [P, Fin.sum_univ_succ] <;> norm_num)
    (by simp [P, obj, Fin.sum_univ_succ])

/-- The origin is the only optimal point. -/
theorem eq_zero_of_isOptimal {x : Fin 3 → ℚ} (h : P.IsOptimal x) : x = 0 := by
  have h0 := h.1 0
  have h1 := h.1 1
  have h2 := h.1 2
  have hz := h.2 0 origin_feasible
  simp [P, obj, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 hz
  funext i
  fin_cases i <;> simp <;> linarith

/-- **L4 has the largest projection of the objective vector.** -/
theorem L4_isMaxProjection : P.IsMaxProjection 3 := by
  refine ⟨by simp [P, dotProduct, Fin.sum_univ_succ], fun i hi hpos => ?_⟩
  fin_cases i <;> simp_all [P, dotProduct, Fin.sum_univ_succ] <;>
    (try norm_num at hpos) <;> norm_num

/-- **L4 is not a principal hyperface.** -/
theorem L4_not_principal : ¬ P.IsPrincipal 3 := by
  rintro ⟨x, hx, hact⟩
  rw [eq_zero_of_isOptimal hx] at hact
  simp [Active, P] at hact

/-- **No constraint is redundant.** -/
theorem not_redundant : ∀ i, ¬ P.Redundant i := by
  intro i h
  fin_cases i
  · have := h ![1, 0, 0] (fun i hi => by fin_cases i <;> simp_all [P])
    norm_num [P, dotProduct, Fin.sum_univ_succ] at this
  · have := h ![-1/10, 1/10, 0] (fun i hi => by fin_cases i <;> simp_all [P] <;> norm_num)
    norm_num [P, dotProduct, Fin.sum_univ_succ] at this
  · have := h ![-1, -1, 0] (fun i hi => by fin_cases i <;> simp_all [P]; norm_num)
    norm_num [P, dotProduct, Fin.sum_univ_succ] at this
  · have := h ![1, 2, -1] (fun i hi => by fin_cases i <;> simp_all [P] <;> norm_num)
    norm_num [P, dotProduct, Fin.sum_univ_succ] at this
  · have := h ![0, 0, -11] (fun i hi => by fin_cases i <;> simp_all [P]; norm_num)
    norm_num [P, dotProduct, Fin.sum_univ_succ] at this

/-- The feasible set is bounded, so the example is a genuine polytope. -/
theorem bounded {x : Fin 3 → ℚ} (hx : P.Feasible x) :
    |x 0| ≤ 20 ∧ |x 1| ≤ 20 ∧ -10 ≤ x 2 ∧ x 2 ≤ 0 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h4 := hx 4
  simp [P, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h4
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    by linarith, by linarith⟩

/-- **The method fails when it follows the projection rule here.** Whatever variable
is eliminated with L4 and whatever is done afterwards, the returned point is not
optimal. -/
theorem method_fails (j : Fin 3) (hk : P.A 3 j ≠ 0) (y : Fin 2 → ℚ) :
    ¬ P.IsOptimal (P.lift 3 j y) :=
  P.not_isOptimal_lift 3 j hk L4_not_principal y

end PotapovSat.LP.ProjectionCounterexample
