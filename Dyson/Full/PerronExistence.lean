import Dyson.Full.SingularitiesPerronLimit

/-! The only external premise in this module is the ordinary finite-dimensional
Perron--Frobenius existence and simplicity theorem. Preservation of the
manuscript's actual positive-power irreducibility under positive diagonal
scaling, its application to |m|S|m|, and the eigenvalue-one conclusion at an
actual regular frontier point are proved internally. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Singularities
open Manuscript.PositivityCorrection

/-- Standard Perron--Frobenius theorem for an irreducible nonnegative finite
matrix, stated independently of any Dyson equation, boundary, or density.
The left/right normalization determines the coefficient in the simple complex
eigenspace. -/
def ExternalPerronExistence : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (F : Matrix (Fin n) (Fin n) ℝ),
    Nonnegative F → Manuscript.PositivityCorrection.Irreducible F →
    ∃ (lam : ℝ) (r l : Fin n → ℝ), 0 ≤ lam ∧
      (∀ i, 0 < r i) ∧ (∀ i, 0 < l i) ∧
      (∑ i, l i * r i = 1) ∧
      (∀ i, ∑ j, F i j * r j = lam * r i) ∧
      (∀ j, ∑ i, l i * F i j = lam * l j) ∧
      ∀ x : Fin n → ℂ, Model.action F x = (lam : ℂ) • x →
        x = (∑ i, (l i : ℂ) * x i) • (fun i => (r i : ℂ))

/-- Positive matrix-power entries transfer whenever positive support edges
transfer between two nonnegative matrices. The exponent is preserved, including
positive return paths on the diagonal. -/
theorem positive_power_transfer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hB : Nonnegative B)
    (hsupport : ∀ i j, 0 < A i j → 0 < B i j)
    (k : ℕ) (i j : Fin n) (hpos : 0 < (A ^ k) i j) : 0 < (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simpa using hpos
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply] at hpos ⊢
    have hex : ∃ t : Fin n, 0 < A i t * (A ^ k) t j := by
      by_contra h
      push_neg at h
      exact (not_lt_of_ge (Finset.sum_nonpos (fun t _ => h t))) hpos
    obtain ⟨t, ht⟩ := hex
    have hedge : 0 < A i t := by
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_gt h) (power_nonnegative A hA k t j))) ht
    have hrest : 0 < (A ^ k) t j := by
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
        (hA i t) (le_of_not_gt h))) ht
    exact Finset.sum_pos'
      (fun t _ => mul_nonneg (hB i t) (power_nonnegative B hB k t j))
      ⟨t, Finset.mem_univ t, mul_pos (hsupport i t hedge) (ih t j hrest)⟩

/-- The true saturated matrix, with the actual norms of the solution. -/
def saturatedMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ‖m i‖ * S i j * ‖m j‖

theorem saturatedMatrix_nonnegative {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (m : Fin n → ℂ) : Nonnegative (saturatedMatrix S m) :=
  fun i j => mul_nonneg (mul_nonneg (norm_nonneg _) (hS i j)) (norm_nonneg _)

theorem saturatedMatrix_positive_support {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℂ) (hm : ∀ i, m i ≠ 0) (i j : Fin n) :
    0 < saturatedMatrix S m i j ↔ 0 < S i j := by
  unfold saturatedMatrix
  rw [mul_pos_iff_of_pos_right (norm_pos_iff.mpr (hm j)),
    mul_pos_iff_of_pos_left (norm_pos_iff.mpr (hm i))]

/-- The manuscript's positive-power irreducibility, rather than merely
connectivity of a replacement graph, holds for the actual saturated matrix. -/
theorem saturatedMatrix_irreducible {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S) (m : Fin n → ℂ)
    (hm : ∀ i, m i ≠ 0) : Manuscript.PositivityCorrection.Irreducible (saturatedMatrix S m) := by
  intro i j
  obtain ⟨k, hk, hpos⟩ := hirr i j
  refine ⟨k, hk, positive_power_transfer S (saturatedMatrix S m) hS
    (saturatedMatrix_nonnegative S hS m) ?_ k i j hpos⟩
  intro i j hij
  exact (saturatedMatrix_positive_support S m hm i j).mpr hij

/-- Actual positive, normalized left and right Perron vectors and the simple
complex eigenspace are obtained from the general matrix theorem. -/
theorem saturatedMatrix_perron_data (external : ExternalPerronExistence)
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S) (m : Fin n → ℂ)
    (hm : ∀ i, m i ≠ 0) :
    ∃ (lam : ℝ) (r l : Fin n → ℝ), 0 ≤ lam ∧
      (∀ i, 0 < r i) ∧ (∀ i, 0 < l i) ∧
      (∑ i, l i * r i = 1) ∧
      (∀ i, ∑ j, saturatedMatrix S m i j * r j = lam * r i) ∧
      (∀ j, ∑ i, l i * saturatedMatrix S m i j = lam * l j) ∧
      ∀ x : Fin n → ℂ, complexMatrixOperator (saturatedMatrix S m) x = (lam : ℂ) • x →
        x = complexFunctional l x • (fun i => (r i : ℂ)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨lam, r, l, hlamnonneg, hr, hl, hnorm, hright, hleft, hsimple⟩ :=
    external n hn (saturatedMatrix S m) (saturatedMatrix_nonnegative S hS m)
      (saturatedMatrix_irreducible S hS hirr m hm)
  refine ⟨lam, r, l, hlamnonneg, hr, hl, hnorm, hright, hleft, ?_⟩
  intro x hx
  simpa [complexFunctional] using hsimple x hx

/-- At an actual regular edge or cusp frontier, the Perron eigenvalue is one.
The measure/support sequence, boundary equations, and eigenvalue limit are
proved internally; no Dyson-specific conclusion is included in the external
Perron assumption. -/
theorem regular_frontier_perron_data (external : ExternalPerronExistence)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ (r l : Fin n → ℝ), (∀ i, 0 < r i) ∧ (∀ i, 0 < l i) ∧
      (∑ i, l i * r i = 1) ∧
      (∀ i, ∑ j, saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)) i j * r j = r i) ∧
      (∀ j, ∑ i, l i * saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)) i j = l j) ∧
      ∀ x : Fin n → ℂ,
        complexMatrixOperator (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ))) x = x →
        x = complexFunctional l x • (fun i => (r i : ℂ)) := by
  have hm := (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  obtain ⟨lam, r, l, _, hr, hl, hnorm, hright, hleft, hsimple⟩ :=
    saturatedMatrix_perron_data external hn S hS hirr _ hm
  have hlam : lam = 1 := regular_frontier_perron_one hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ l lam hl hleft
  subst lam
  refine ⟨r, l, hr, hl, hnorm, ?_, ?_, ?_⟩
  · simpa using hright
  · simpa using hleft
  · intro x hx
    exact hsimple x (by simpa using hx)

end NonSymmetricDyson.Full.Singularities
