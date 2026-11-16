import PotapovSat.LP.Basic

/-!
# Cone obstruction for non-redundant constraints

The method of principal hyperfaces assumes that the system of inequalities
"does not contain superfluous constraints" (I. Yu. Grishin, 2008). This file makes
that assumption precise and draws its main geometric consequence.

At an optimal vertex, the objective vector lies in the cone spanned by the normals of
the active constraints. The selection rule of the method prefers the constraint whose
normal makes the smallest angle with the objective vector. The lemma below shows what
cannot happen under non-redundancy: the normal of a non-redundant constraint never lies
in the cone spanned by the normals of *other* constraints that are active at a common
feasible point.

## Main results

* `Problem.redundant_of_mem_activeCone`: if `A k` is a non-negative combination of
  normals of other constraints active at a feasible point, then `k` is redundant.
* `Problem.not_mem_activeCone`: the contrapositive, for non-redundant systems.
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Problem

variable {n : ℕ} {ι : Type*} [Fintype ι] (P : Problem K n ι)

/-- If the normal of constraint `k` is a non-negative combination of the normals of
other constraints that are all active at a feasible point `x`, then constraint `k` is
implied by the remaining constraints. -/
theorem redundant_of_mem_activeCone (k : ι) (μ : ι → K) (hμ : ∀ i, 0 ≤ μ i)
    (hμk : μ k = 0) (hcomb : ∀ j, ∑ i, μ i * P.A i j = P.A k j)
    {x : Fin n → K} (hx : P.Feasible x) (hact : ∀ i, μ i ≠ 0 → P.Active i x) :
    P.Redundant k := by
  intro w hw
  have hw' : P.A k ⬝ᵥ w ≤ ∑ i, μ i * P.b i := by
    rw [P.comb_dot μ (P.A k) hcomb w]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : i = k
    · subst hik
      simp [hμk]
    · exact mul_le_mul_of_nonneg_left (hw i hik) (hμ i)
  have hx' : P.A k ⬝ᵥ x = ∑ i, μ i * P.b i := by
    rw [P.comb_dot μ (P.A k) hcomb x]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : μ i = 0
    · simp [hi]
    · rw [hact i hi]
  linarith [hx k]

/-- **Cone obstruction.** In a system without redundant constraints, the normal of a
constraint never lies in the cone spanned by the normals of other constraints that are
active at a common feasible point. -/
theorem not_mem_activeCone (k : ι) (hk : ¬ P.Redundant k) (μ : ι → K)
    (hμ : ∀ i, 0 ≤ μ i) (hμk : μ k = 0) (hcomb : ∀ j, ∑ i, μ i * P.A i j = P.A k j)
    {x : Fin n → K} (hx : P.Feasible x) : ¬ ∀ i, μ i ≠ 0 → P.Active i x :=
  fun hact => hk (P.redundant_of_mem_activeCone k μ hμ hμk hcomb hx hact)

end Problem

end PotapovSat.LP
