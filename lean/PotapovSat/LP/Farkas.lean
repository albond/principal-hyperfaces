import PotapovSat.LP.Basic

/-!
# Farkas' lemma over an ordered field, by Fourier–Motzkin elimination

For a finite system of linear inequalities `A i ⬝ᵥ x ≤ b i` over a linearly ordered
field, exactly one of the following holds:

* the system has a solution;
* there are multipliers `y ≥ 0` with `∑ i, y i • A i = 0` and `∑ i, y i * b i < 0`
  (a certificate that the system is unsolvable).

The proof is by induction on the number of variables. One step eliminates the last
variable by adding pairs of inequalities in which it has opposite signs
(Fourier–Motzkin elimination). Like the principal-hyperface method, it reduces the
dimension by one at a time, using non-negative combinations of the constraints.

## Main results

* `not_solvable_of_certificate`: a certificate rules out solutions.
* `farkas`: every finite system is either solvable or has a certificate.
* `solvable_iff`: solvability is equivalent to the absence of a certificate.
-/

namespace PotapovSat.LP

universe u

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The system `A i ⬝ᵥ x ≤ b i` has a solution. -/
def Solvable {n : ℕ} {ι : Type*} (A : ι → Fin n → K) (b : ι → K) : Prop :=
  ∃ x, ∀ i, A i ⬝ᵥ x ≤ b i

/-- `y` certifies that the system `A i ⬝ᵥ x ≤ b i` has no solution. -/
def InfeasibilityCertificate {n : ℕ} {ι : Type*} [Fintype ι] (A : ι → Fin n → K)
    (b : ι → K) (y : ι → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i < 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem sum_mul_dot {n : ℕ} {ι : Type*} [Fintype ι] (μ : ι → K) (A : ι → Fin n → K)
    (x : Fin n → K) :
    ∑ j, (∑ i, μ i * A i j) * x j = ∑ i, μ i * (A i ⬝ᵥ x) := by
  simp only [dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A certificate rules out solutions. -/
theorem not_solvable_of_certificate {n : ℕ} {ι : Type*} [Fintype ι] {A : ι → Fin n → K}
    {b : ι → K} {y : ι → K} (hy : InfeasibilityCertificate A b y) : ¬ Solvable A b := by
  rintro ⟨x, hx⟩
  obtain ⟨hy0, hyA, hyb⟩ := hy
  have h1 : ∑ i, y i * (A i ⬝ᵥ x) = 0 := by
    rw [← sum_mul_dot]
    simp [hyA]
  have h2 : ∑ i, y i * (A i ⬝ᵥ x) ≤ ∑ i, y i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy0 i)
  linarith

omit [IsStrictOrderedRing K] in
/-- Between two finite families with every lower value below every upper value, there is
a common separating point. -/
theorem exists_between_finset {α : Type*} (s t : Finset α) (f : α → K)
    (h : ∀ p ∈ s, ∀ q ∈ t, f p ≤ f q) :
    ∃ x : K, (∀ p ∈ s, f p ≤ x) ∧ ∀ q ∈ t, x ≤ f q := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨0, by simp [hs], by simp [ht]⟩
    · obtain ⟨q₀, -, hmin⟩ := t.exists_min_image f ht
      exact ⟨f q₀, by simp [hs], hmin⟩
  · obtain ⟨p₀, hp₀, hmax⟩ := s.exists_max_image f hs
    exact ⟨f p₀, hmax, fun q hq => h p₀ hp₀ q hq⟩

namespace FourierMotzkin

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Fin (n + 1) → K) (b : ι → K)

/-- Multipliers defining the eliminated system. Index `inl i` keeps constraint `i` when
the last variable does not occur in it. Index `inr (p, q)` combines a constraint `p`
with positive and a constraint `q` with negative last coefficient. -/
def lam : ι ⊕ (ι × ι) → ι → K
  | .inl i => fun i₀ => if A i (Fin.last n) = 0 then (if i₀ = i then 1 else 0) else 0
  | .inr (p, q) => fun i₀ =>
      if 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0 then
        (if i₀ = p then -A q (Fin.last n) else 0) + (if i₀ = q then A p (Fin.last n) else 0)
      else 0

/-- Coefficients of the eliminated system (in the first `n` variables). -/
def A' (κ : ι ⊕ (ι × ι)) (j : Fin n) : K := ∑ i, lam A κ i * A i j.castSucc

/-- Right-hand sides of the eliminated system. -/
def b' (κ : ι ⊕ (ι × ι)) : K := ∑ i, lam A κ i * b i

omit [Fintype ι] in
theorem lam_nonneg (κ : ι ⊕ (ι × ι)) (i₀ : ι) : 0 ≤ lam A κ i₀ := by
  rcases κ with i | ⟨p, q⟩
  · simp only [lam]
    split_ifs <;> norm_num
  · by_cases h : 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0
    · have h1 := h.1
      have h2 := h.2
      simp only [lam, h, and_self, ite_true]
      split_ifs <;> linarith
    · simp [lam, h]

omit [IsStrictOrderedRing K] in
theorem sum_lam_inl (v : ι → K) (i : ι) :
    ∑ i₀, lam A (.inl i) i₀ * v i₀ = if A i (Fin.last n) = 0 then v i else 0 := by
  simp only [lam]
  split_ifs <;> simp

omit [IsStrictOrderedRing K] in
theorem sum_lam_inr (v : ι → K) (p q : ι) :
    ∑ i₀, lam A (.inr (p, q)) i₀ * v i₀ =
      if 0 < A p (Fin.last n) ∧ A q (Fin.last n) < 0 then
        -A q (Fin.last n) * v p + A p (Fin.last n) * v q
      else 0 := by
  simp only [lam]
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]

omit [IsStrictOrderedRing K] in
/-- The eliminated variable cancels in every derived constraint. -/
theorem sum_lam_last (κ : ι ⊕ (ι × ι)) : ∑ i, lam A κ i * A i (Fin.last n) = 0 := by
  rcases κ with i | ⟨p, q⟩
  · rw [sum_lam_inl]
    split_ifs with h <;> simp [h]
  · rw [sum_lam_inr]
    split_ifs <;> ring

omit [IsStrictOrderedRing K] in
theorem A'_dot (κ : ι ⊕ (ι × ι)) (x' : Fin n → K) :
    A' A κ ⬝ᵥ x' = ∑ i, lam A κ i * ((fun j => A i j.castSucc) ⬝ᵥ x') := by
  simp only [dotProduct, A', Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] [DecidableEq ι] in
theorem dot_snoc (u : Fin (n + 1) → K) (x' : Fin n → K) (t : K) :
    u ⬝ᵥ (Fin.snoc x' t : Fin (n + 1) → K) =
      (fun j => u j.castSucc) ⬝ᵥ x' + u (Fin.last n) * t := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- **Lifting solutions.** A solution of the eliminated system extends to a solution of
the original system. -/
theorem solvable_of_reduced (h : Solvable (A' A) (b' A b)) : Solvable A b := by
  obtain ⟨x', hx'⟩ := h
  set a : ι → K := fun i => A i (Fin.last n) with ha
  set r : ι → K := fun i => b i - (fun j => A i j.castSucc) ⬝ᵥ x' with hr
  have hpair : ∀ p ∈ Finset.univ.filter (fun i => a i < 0),
      ∀ q ∈ Finset.univ.filter (fun i => 0 < a i), r p / a p ≤ r q / a q := by
    intro p hp q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hrow := hx' (.inr (q, p))
    rw [A'_dot, sum_lam_inr, b', sum_lam_inr] at hrow
    rw [ite_eq_left (show 0 < A q (Fin.last n) ∧ A p (Fin.last n) < 0 from ⟨hq, hp⟩),
      ite_eq_left (show 0 < A q (Fin.last n) ∧ A p (Fin.last n) < 0 from ⟨hq, hp⟩)] at hrow
    rw [le_div_iff₀ hq, div_mul_eq_mul_div, div_le_iff_of_neg hp]
    simp only [hr]
    linarith
  obtain ⟨t, hlo, hup⟩ := exists_between_finset _ _ (fun i => r i / a i) hpair
  refine ⟨Fin.snoc x' t, fun i => ?_⟩
  rw [dot_snoc]
  rcases lt_trichotomy (a i) 0 with hneg | hzero | hpos
  · have := hlo i (by simp [hneg])
    rw [div_le_iff_of_neg hneg] at this
    simp only [hr, ha] at this hneg ⊢
    linarith
  · have hrow := hx' (.inl i)
    rw [A'_dot, sum_lam_inl, b', sum_lam_inl] at hrow
    simp only [ha] at hzero
    simp only [hzero, ite_true] at hrow
    rw [hzero, zero_mul, add_zero]
    exact hrow
  · have := hup i (by simp [hpos])
    rw [le_div_iff₀ hpos] at this
    simp only [hr, ha] at this hpos ⊢
    linarith

/-- **Pulling back certificates.** A certificate for the eliminated system gives a
certificate for the original system. -/
theorem certificate_of_reduced (y' : ι ⊕ (ι × ι) → K)
    (hy : InfeasibilityCertificate (A' A) (b' A b) y') :
    InfeasibilityCertificate A b (fun i => ∑ κ, y' κ * lam A κ i) := by
  obtain ⟨hy0, hyA, hyb⟩ := hy
  have key : ∀ v : ι → K, ∑ i, (∑ κ, y' κ * lam A κ i) * v i
      = ∑ κ, y' κ * ∑ i, lam A κ i * v i := by
    intro v
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  refine ⟨fun i => Finset.sum_nonneg fun κ _ => mul_nonneg (hy0 κ) (lam_nonneg A κ i),
    fun j => ?_, ?_⟩
  · rw [key (fun i => A i j)]
    induction j using Fin.lastCases with
    | last => simp [sum_lam_last]
    | cast j' => exact hyA j'
  · rw [key b]
    exact hyb

end FourierMotzkin

/-- **Farkas' lemma.** A finite system of linear inequalities over a linearly ordered
field is either solvable or has a certificate of unsolvability. -/
theorem farkas (n : ℕ) : ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin n → K) (b : ι → K),
    Solvable A b ∨ ∃ y, InfeasibilityCertificate A b y := by
  induction n with
  | zero =>
    intro ι _ _ A b
    by_cases h : ∀ i, 0 ≤ b i
    · exact Or.inl ⟨Fin.elim0, fun i => by simpa [dotProduct] using h i⟩
    · simp only [not_forall, not_le] at h
      obtain ⟨i, hi⟩ := h
      refine Or.inr ⟨fun i₀ => if i₀ = i then 1 else 0, fun i₀ => ?_, fun j => j.elim0, ?_⟩
      · dsimp only
        split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ _ A b
    rcases ih (FourierMotzkin.A' A) (FourierMotzkin.b' A b) with h | ⟨y', hy'⟩
    · exact Or.inl (FourierMotzkin.solvable_of_reduced A b h)
    · exact Or.inr ⟨_, FourierMotzkin.certificate_of_reduced A b y' hy'⟩

/-- Solvability is equivalent to the absence of a certificate of unsolvability. -/
theorem solvable_iff {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin n → K) (b : ι → K) :
    Solvable A b ↔ ∀ y, ¬ InfeasibilityCertificate A b y := by
  constructor
  · exact fun h y hy => not_solvable_of_certificate hy h
  · intro h
    rcases farkas n A b with hs | ⟨y, hy⟩
    · exact hs
    · exact absurd hy (h y)

end PotapovSat.LP
