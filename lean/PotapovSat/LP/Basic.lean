import Mathlib

/-!
# Linear programs in inequality form

We study problems of the form

  maximize `c ⬝ᵥ x` subject to `A i ⬝ᵥ x ≤ b i` for every constraint index `i`,

over an arbitrary linearly ordered field `K` (for example `ℚ` or `ℝ`).

This file fixes the vocabulary used for the method of principal hyperfaces
(G. G. Potapov, I. Yu. Grishin, 2007; I. Yu. Grishin, 2008):

* `Problem.Feasible`, `Problem.IsOptimal`, `Problem.Active`;
* `Problem.IsPrincipal k`: constraint `k` is a *principal hyperface*, i.e. it is
  active at some optimal point;
* `Problem.Redundant k`: constraint `k` is implied by the others;
* `Problem.IsMaxProjection k`: constraint `k` maximises the projection
  `(c ⬝ᵥ A k) / ‖A k‖` of the objective vector onto the constraint normal,
  the selection rule used by the method;
* weak duality and the resulting certificate of optimality.
-/

namespace PotapovSat.LP

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A linear program `max c ⬝ᵥ x` s.t. `A i ⬝ᵥ x ≤ b i`, with `n` variables and
constraints indexed by `ι`. -/
structure Problem (K : Type*) (n : ℕ) (ι : Type*) where
  /-- Objective vector. -/
  c : Fin n → K
  /-- Constraint normals. -/
  A : ι → Fin n → K
  /-- Right-hand sides. -/
  b : ι → K

namespace Problem

variable {n : ℕ} {ι : Type*} (P : Problem K n ι)

/-- `x` satisfies every constraint. -/
def Feasible (x : Fin n → K) : Prop := ∀ i, P.A i ⬝ᵥ x ≤ P.b i

/-- Objective value. -/
def obj (x : Fin n → K) : K := P.c ⬝ᵥ x

/-- `x` is an optimal (maximising) feasible point. -/
def IsOptimal (x : Fin n → K) : Prop :=
  P.Feasible x ∧ ∀ y, P.Feasible y → P.obj y ≤ P.obj x

/-- Constraint `i` holds with equality at `x`. -/
def Active (i : ι) (x : Fin n → K) : Prop := P.A i ⬝ᵥ x = P.b i

/-- Constraint `k` is a *principal hyperface*: it is active at some optimal point. -/
def IsPrincipal (k : ι) : Prop := ∃ x, P.IsOptimal x ∧ P.Active k x

/-- Constraint `k` is implied by the other constraints. -/
def Redundant (k : ι) : Prop :=
  ∀ x, (∀ i, i ≠ k → P.A i ⬝ᵥ x ≤ P.b i) → P.A k ⬝ᵥ x ≤ P.b k

/-- Constraint `k` has the strictly largest positive projection `(c ⬝ᵥ A k) / ‖A k‖`
of the objective vector onto its normal. Stated without square roots: for positive
projections, comparing `p_i / ‖A i‖` is the same as comparing `p_i ^ 2 / ‖A i‖ ^ 2`. -/
def IsMaxProjection (k : ι) : Prop :=
  0 < P.c ⬝ᵥ P.A k ∧
    ∀ i, i ≠ k → 0 < P.c ⬝ᵥ P.A i →
      (P.c ⬝ᵥ P.A i) ^ 2 * (P.A k ⬝ᵥ P.A k) < (P.c ⬝ᵥ P.A k) ^ 2 * (P.A i ⬝ᵥ P.A i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A combination of rows, dotted with `x`. -/
theorem comb_dot [Fintype ι] (μ : ι → K) (v : Fin n → K)
    (hv : ∀ j, ∑ i, μ i * P.A i j = v j) (x : Fin n → K) :
    v ⬝ᵥ x = ∑ i, μ i * (P.A i ⬝ᵥ x) := by
  calc v ⬝ᵥ x = ∑ j, v j * x j := rfl
    _ = ∑ j, (∑ i, μ i * P.A i j) * x j := by simp_rw [hv]
    _ = ∑ i, μ i * (P.A i ⬝ᵥ x) := by
      simp only [dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm

/-- **Weak duality.** If `y ≥ 0` and `∑ i, y i • A i = c`, then `c ⬝ᵥ x ≤ ∑ i, y i * b i`
for every feasible `x`. -/
theorem weak_duality [Fintype ι] (y : ι → K) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ j, ∑ i, y i * P.A i j = P.c j) {x : Fin n → K} (hx : P.Feasible x) :
    P.obj x ≤ ∑ i, y i * P.b i := by
  rw [obj, P.comb_dot y P.c hc x]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy i)

/-- **Certificate of optimality.** A feasible point whose value equals the value of a
dual-feasible vector is optimal. -/
theorem isOptimal_of_certificate [Fintype ι] {x : Fin n → K} (hx : P.Feasible x)
    (y : ι → K) (hy : ∀ i, 0 ≤ y i) (hc : ∀ j, ∑ i, y i * P.A i j = P.c j)
    (hval : P.obj x = ∑ i, y i * P.b i) : P.IsOptimal x :=
  ⟨hx, fun _ hz => hval ▸ P.weak_duality y hy hc hz⟩

end Problem

end PotapovSat.LP
