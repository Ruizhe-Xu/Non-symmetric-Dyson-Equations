import Dyson.BasicEstimates

/-!
Polynomial presentation of the Dyson equation.  This presentation can be
passed to limits without first establishing nonvanishing of the limit.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.PolynomialDyson

variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ} {m : ι → ℂ}

/-- Multiplying the Dyson equation by its component clears the inverse. -/
def IsPolynomialSolution (S : ι → ι → ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ) : Prop :=
  ∀ i, (-1 : ℂ) = m i * (z - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j)

theorem component_ne_zero (hpoly : IsPolynomialSolution S a z m) (i : ι) :
    m i ≠ 0 := by
  intro hi
  have h := hpoly i
  simp [hi] at h

/-- The polynomial form itself guarantees that denominators are nonzero. -/
theorem to_dyson (hpoly : IsPolynomialSolution S a z m) :
    BasicEstimates.IsDysonSolution S a z m := by
  intro i
  have h := congrArg (fun x : ℂ => (m i)⁻¹ * x) (hpoly i)
  simpa only [mul_neg, mul_one, ← mul_assoc,
    inv_mul_cancel₀ (component_ne_zero hpoly i), one_mul] using h

/-- Any ordinary solution with nonzero components has the polynomial form. -/
theorem of_dyson (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hmzero : ∀ i, m i ≠ 0) : IsPolynomialSolution S a z m := by
  intro i
  calc
    (-1 : ℂ) = m i * (-(m i)⁻¹) := by simp [hmzero i]
    _ = m i * (z - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j) :=
      congrArg (fun x : ℂ => m i * x) (hsol i)

/-- At a spectral parameter in the upper half-plane, a polynomial solution
in the closed upper half-plane actually lies in the open upper half-plane. -/
theorem upper_of_nonnegative_imaginary
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hmnonneg : ∀ i, 0 ≤ (m i).im)
    (hpoly : IsPolynomialSolution S a z m) :
    BasicEstimates.IsUpperSolution m := by
  intro i
  have hsum : 0 ≤ ∑ j, S i j * (m j).im :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (hmnonneg j)
  have hquot : 0 < (m i).im / Complex.normSq (m i) := by
    rw [BasicEstimates.imaginary_part_identity (to_dyson hpoly) i]
    exact add_pos_of_pos_of_nonneg hz hsum
  exact (div_pos_iff_of_pos_right
    (Complex.normSq_pos.mpr (component_ne_zero hpoly i))).mp hquot

/-- Both properties required of an upper-half-plane solution follow from the
closed-half-plane polynomial system. -/
theorem upper_solution_of_polynomial
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hmnonneg : ∀ i, 0 ≤ (m i).im)
    (hpoly : IsPolynomialSolution S a z m) :
    BasicEstimates.IsUpperSolution m ∧ BasicEstimates.IsDysonSolution S a z m :=
  ⟨upper_of_nonnegative_imaginary hS hz hmnonneg hpoly, to_dyson hpoly⟩


end NonSymmetricDyson.PolynomialDyson
