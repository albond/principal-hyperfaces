import PotapovSat.LP.Elimination

/-!
# The worked example of Grishin (2008)

I. Yu. Grishin, "Heuristic algorithm for determining principal faces in solving the
linear programming problem", Vestnik NTU "KhPI", 2008, No. 49, pp. 33–41 (in Russian),
solves the resource-allocation problem

  maximize `3x₁ + 4x₂ + 8x₃ + 5x₄ + 12x₅ + 2x₆`

subject to

  L1: `3x₁ + 2x₂ − x₃ + 6x₄ + x₅ + x₆ ≤ 24`
  L2: `x₁ + 6x₂ + x₃ + 2x₆ ≤ 18`
  L3: `x₄ + 2x₅ ≤ 12`
  L4: `3x₄ + x₅ ≤ 12`
  L5: `2x₁ + x₂ + x₃ ≤ 24`
  L6: `2x₃ + x₅ + 3x₆ ≤ 36`
  L7–L12: `−xⱼ ≤ 0`

by the principal-hyperface method, choosing in order the hyperfaces
L3, L2, L6, L12, L8, L4, and reports the optimum `z = 201.6` at
`x = (2.4, 0, 15.6, 2.4, 4.8, 0)`.

We verify that this answer is exactly optimal, with a dual certificate. We also verify
that each hyperface the paper chose is principal, and that the paper's first choice
L3 is the constraint with the largest projection of the objective vector.
Constraint `Lm` has index `m - 1` below.
-/

namespace PotapovSat.LP.Grishin2008

open Problem

/-- The problem from the paper. -/
def P : Problem ℚ 6 (Fin 12) where
  c := ![3, 4, 8, 5, 12, 2]
  A := ![![3, 2, -1, 6, 1, 1], ![1, 6, 1, 0, 0, 2], ![0, 0, 0, 1, 2, 0],
         ![0, 0, 0, 3, 1, 0], ![2, 1, 1, 0, 0, 0], ![0, 0, 2, 0, 1, 3],
         ![-1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0],
         ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, -1]]
  b := ![24, 18, 12, 12, 24, 36, 0, 0, 0, 0, 0, 0]

/-- The optimum reported in the paper. -/
def xStar : Fin 6 → ℚ := ![12/5, 0, 78/5, 12/5, 24/5, 0]

/-- Dual multipliers (computed for this project; not in the paper). -/
def yStar : Fin 12 → ℚ := ![0, 3, 47/10, 1/10, 0, 5/2, 0, 14, 0, 0, 0, 23/2]

theorem xStar_feasible : P.Feasible xStar := by
  intro i
  fin_cases i <;> simp [P, xStar, dotProduct, Fin.sum_univ_succ] <;> norm_num

theorem yStar_dual : ∀ j, ∑ i, yStar i * P.A i j = P.c j := by
  intro j
  fin_cases j <;> simp [P, yStar, Fin.sum_univ_succ] <;> norm_num

theorem value_eq : P.obj xStar = ∑ i, yStar i * P.b i := by
  simp [P, xStar, yStar, obj, dotProduct, Fin.sum_univ_succ]
  norm_num

/-- **The paper's answer is optimal.** -/
theorem xStar_isOptimal : P.IsOptimal xStar :=
  P.isOptimal_of_certificate xStar_feasible yStar
    (fun i => by fin_cases i <;> simp [yStar] <;> norm_num) yStar_dual value_eq

/-- **The optimal value is `1008/5 = 201.6`**, as reported. -/
theorem optimal_value : P.obj xStar = 1008 / 5 := by
  simp [P, xStar, obj, dotProduct, Fin.sum_univ_succ]
  norm_num

/-- **Every hyperface chosen in the paper is principal**: L3, L2, L6, L12, L8, L4. -/
theorem paper_choices_principal :
    P.IsPrincipal 2 ∧ P.IsPrincipal 1 ∧ P.IsPrincipal 5 ∧
      P.IsPrincipal 11 ∧ P.IsPrincipal 7 ∧ P.IsPrincipal 3 := by
  refine ⟨⟨xStar, xStar_isOptimal, ?_⟩, ⟨xStar, xStar_isOptimal, ?_⟩,
    ⟨xStar, xStar_isOptimal, ?_⟩, ⟨xStar, xStar_isOptimal, ?_⟩,
    ⟨xStar, xStar_isOptimal, ?_⟩, ⟨xStar, xStar_isOptimal, ?_⟩⟩ <;>
  norm_num [Active, P, xStar, dotProduct, Fin.sum_univ_succ]

/-- **The first choice follows the projection rule**: L3 has the largest projection
`(c ⬝ᵥ A₃) / ‖A₃‖ = 29 / √5`. -/
theorem L3_isMaxProjection : P.IsMaxProjection 2 := by
  refine ⟨by simp [P, dotProduct, Fin.sum_univ_succ]; norm_num, fun i hi hpos => ?_⟩
  fin_cases i <;> simp_all [P, dotProduct, Fin.sum_univ_succ] <;>
    (try norm_num at hpos) <;> norm_num

end PotapovSat.LP.Grishin2008
