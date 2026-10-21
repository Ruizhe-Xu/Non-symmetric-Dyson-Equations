import Mathlib
import Dyson.BasicEstimates
import Dyson.StrictWeight
import Dyson.WeightedMaximum

/-!
Uniqueness of an upper-half-plane solution of the finite vector Dyson equation.
The argument applies to arbitrary finite nonnegative real coefficient matrices;
it does not require symmetry or irreducibility.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.Uniqueness

open BasicEstimates

variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ} {m n : ι → ℂ}

/-- Exact difference equation for two actual solutions at the same `z`. -/
theorem difference_identity (hm : IsUpperSolution m) (hn : IsUpperSolution n)
    (hmsol : IsDysonSolution S a z m) (hnsol : IsDysonSolution S a z n)
    (i : ι) :
    n i - m i = m i * n i * ∑ j, (S i j : ℂ) * (n j - m j) := by
  have hm0 := component_ne_zero hm i
  have hn0 := component_ne_zero hn i
  have hdiff : (n i - m i) / (m i * n i) =
      ∑ j, (S i j : ℂ) * (n j - m j) := by
    calc
      (n i - m i) / (m i * n i) = -(n i)⁻¹ - (-(m i)⁻¹) := by
        field_simp [hm0, hn0]
        ring
      _ = ∑ j, (S i j : ℂ) * (n j - m j) := by
        rw [hnsol i, hmsol i]
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        ring
  calc
    n i - m i = (∑ j, (S i j : ℂ) * (n j - m j)) * (m i * n i) :=
      (div_eq_iff (mul_ne_zero hm0 hn0)).mp hdiff
    _ = m i * n i * ∑ j, (S i j : ℂ) * (n j - m j) := mul_comm _ _

/-- The norm inequality obtained from the exact difference equation. -/
theorem difference_norm_le (hS : ∀ i j, 0 ≤ S i j)
    (hm : IsUpperSolution m) (hn : IsUpperSolution n)
    (hmsol : IsDysonSolution S a z m) (hnsol : IsDysonSolution S a z n)
    (i : ι) :
    ‖n i - m i‖ ≤ ∑ j, (‖m i‖ * ‖n i‖ * S i j) * ‖n j - m j‖ := by
  calc
    ‖n i - m i‖ = (‖m i‖ * ‖n i‖) *
        ‖∑ j, (S i j : ℂ) * (n j - m j)‖ := by
      rw [difference_identity hm hn hmsol hnsol i, norm_mul, norm_mul]
    _ ≤ (‖m i‖ * ‖n i‖) * ∑ j, ‖(S i j : ℂ) * (n j - m j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j, (‖m i‖ * ‖n i‖ * S i j) * ‖n j - m j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i j)]
      ring

/-- The uniqueness part of the paper's existence-and-uniqueness theorem.
The only matrix hypothesis is entrywise nonnegativity. -/
theorem upper_half_plane_unique (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : IsUpperSolution m) (hn : IsUpperSolution n)
    (hmsol : IsDysonSolution S a z m) (hnsol : IsDysonSolution S a z n) :
    m = n := by
  let A : ι → ι → ℝ := fun i j => ‖m i‖ * ‖n i‖ * S i j
  let w : ι → ℝ := fun i => Real.sqrt ((m i).im * (n i).im)
  let u : ι → ℝ := fun i => ‖n i - m i‖
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hS i j)
  have hwpos : ∀ i, 0 < w i := fun i => Real.sqrt_pos.mpr (mul_pos (hm i) (hn i))
  have hw : ∀ i, (∑ j, A i j * w j) < w i := by
    intro i
    have hmnorm : 0 < ‖m i‖ := norm_pos_iff.mpr (component_ne_zero hm i)
    have hnnorm : 0 < ‖n i‖ := norm_pos_iff.mpr (component_ne_zero hn i)
    have hmimag : (m i).im = ‖m i‖ ^ 2 *
        (z.im + ∑ j, S i j * (m j).im) := by
      simpa only [Complex.normSq_eq_norm_sq] using
        weighted_imaginary_part_identity hm hmsol i
    have hnimag : (n i).im = ‖n i‖ ^ 2 *
        (z.im + ∑ j, S i j * (n j).im) := by
      simpa only [Complex.normSq_eq_norm_sq] using
        weighted_imaginary_part_identity hn hnsol i
    calc
      (∑ j, A i j * w j) = ‖m i‖ * ‖n i‖ *
          (∑ j, S i j * Real.sqrt ((m j).im * (n j).im)) := by
        dsimp only [A, w]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ < w i := UniquenessAux.strict_geometric_mean_row (S i)
        (fun j => (m j).im) (fun j => (n j).im) (hS i)
        (fun j => le_of_lt (hm j)) (fun j => le_of_lt (hn j))
        z.im ‖m i‖ ‖n i‖ (m i).im (n i).im hz hmnorm hnnorm hmimag hnimag
  have hu : ∀ i, u i ≤ ∑ j, A i j * u j :=
    difference_norm_le hS hm hn hmsol hnsol
  have hzero : ∀ i, u i = 0 := UniquenessAux.eq_zero_of_strict_weight A w u
    hA hwpos (fun i => norm_nonneg _) hu hw
  ext i
  exact (sub_eq_zero.mp (norm_eq_zero.mp (hzero i))).symm


end NonSymmetricDyson.Uniqueness
