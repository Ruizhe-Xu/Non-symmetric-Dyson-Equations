import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators

/-!
# Elementary estimates for a nonsymmetric vector Dyson equation

Source: `main-article-1014.tex`, equation `eq:QVE`, identity
`eq:QVE-imag-bound`, and the bound `eq.rough-boundedness`.

These statements concern any upper-half-plane solution.  They do not assert
existence, uniqueness, analyticity, or a Stieltjes representation.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.BasicEstimates

variable {ι : Type*} [Fintype ι]

/-- The componentwise equation `-1/m = z - a + S m`. -/
def IsDysonSolution (S : ι → ι → ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ) : Prop :=
  ∀ i, -(m i)⁻¹ = z - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j

/-- Every component lies in the open upper half-plane. -/
def IsUpperSolution (m : ι → ℂ) : Prop :=
  ∀ i, 0 < (m i).im

variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ} {m : ι → ℂ}

omit [Fintype ι] in
theorem component_ne_zero (hm : IsUpperSolution m) (i : ι) : m i ≠ 0 := by
  intro h
  have hpos := hm i
  simp [h] at hpos

/-- Taking imaginary parts gives exactly the paper's `eq:QVE-imag-bound`.
`Complex.normSq w` is the squared complex modulus `|w|²`. -/
theorem imaginary_part_identity (hsol : IsDysonSolution S a z m) (i : ι) :
    (m i).im / Complex.normSq (m i) = z.im + ∑ j, S i j * (m j).im := by
  have h := congrArg Complex.im (hsol i)
  simpa [Complex.inv_im, Complex.mul_im, neg_div] using h

/-- The identical formula written using the squared norm. -/
theorem imaginary_part_identity_sq_norm (hsol : IsDysonSolution S a z m) (i : ι) :
    (m i).im / ‖m i‖ ^ 2 = z.im + ∑ j, S i j * (m j).im := by
  simpa only [Complex.normSq_eq_norm_sq] using imaginary_part_identity hsol i

/-- Multiplying by the squared norm gives the weighted imaginary-part equation. -/
theorem weighted_imaginary_part_identity (hm : IsUpperSolution m)
    (hsol : IsDysonSolution S a z m) (i : ι) :
    (m i).im = Complex.normSq (m i) *
      (z.im + ∑ j, S i j * (m j).im) := by
  have hn : Complex.normSq (m i) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (component_ne_zero hm i))
  calc
    (m i).im = (z.im + ∑ j, S i j * (m j).im) * Complex.normSq (m i) :=
      (div_eq_iff hn).mp (imaginary_part_identity hsol i)
    _ = Complex.normSq (m i) * (z.im + ∑ j, S i j * (m j).im) := mul_comm _ _

/-- Each component obeys the elementary bound `|mᵢ(z)| ≤ (Im z)⁻¹`.
No symmetry, irreducibility, or probability representation is required. -/
theorem rough_bound (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : IsUpperSolution m)
    (hsol : IsDysonSolution S a z m) (i : ι) :
    ‖m i‖ ≤ z.im⁻¹ := by
  have hsum : 0 ≤ ∑ j, S i j * (m j).im :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (le_of_lt (hm j))
  have him : z.im ≤ (-(m i)⁻¹).im := by
    rw [hsol i]
    simpa [Complex.mul_im] using le_add_of_nonneg_right hsum (a := z.im)
  have hnorm : z.im ≤ ‖m i‖⁻¹ := by
    calc
      z.im ≤ (-(m i)⁻¹).im := him
      _ ≤ ‖-(m i)⁻¹‖ := Complex.im_le_norm _
      _ = ‖m i‖⁻¹ := by simp [← one_div, Complex.norm_def]
  exact (le_inv_comm₀ hz (norm_pos_iff.mpr (component_ne_zero hm i))).mp hnorm


end NonSymmetricDyson.BasicEstimates
