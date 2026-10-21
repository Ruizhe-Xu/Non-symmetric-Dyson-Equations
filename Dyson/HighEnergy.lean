import Mathlib
import Dyson.BasicEstimates
import Dyson.PolynomialDyson

/-! Quantitative high-imaginary-energy normalization of actual Dyson solutions. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace NonSymmetricDyson.HighEnergy
variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ} {m : ι → ℂ}

theorem normalization_identity (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    z * m i + 1 = (a i : ℂ) * m i - m i * ∑ j, (S i j : ℂ) * m j := by
  have hp := PolynomialDyson.of_dyson hsol (BasicEstimates.component_ne_zero hm) i
  linear_combination -hp

theorem normalization_error_bound (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    ‖z * m i + 1‖ ≤ |a i| * z.im⁻¹ + (∑ j, S i j) * (z.im⁻¹)^2 := by
  have hrough := BasicEstimates.rough_bound hS hz hm hsol
  have hsum : ‖∑ j, (S i j : ℂ) * m j‖ ≤ (∑ j, S i j) * z.im⁻¹ := by
    calc
      _ ≤ ∑ j, ‖(S i j : ℂ) * m j‖ := norm_sum_le _ _
      _ = ∑ j, S i j * ‖m j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i j)]
      _ ≤ ∑ j, S i j * z.im⁻¹ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hrough j) (hS i j))
      _ = _ := (Finset.sum_mul _ _ _).symm
  rw [normalization_identity hm hsol]
  calc
    _ ≤ ‖(a i : ℂ) * m i‖ + ‖m i * ∑ j, (S i j : ℂ) * m j‖ := norm_sub_le _ _
    _ = |a i| * ‖m i‖ + ‖m i‖ * ‖∑ j, (S i j : ℂ) * m j‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |a i| * z.im⁻¹ + z.im⁻¹ * ((∑ j, S i j) * z.im⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_left (hrough i) (abs_nonneg _))
        (mul_le_mul (hrough i) hsum (norm_nonneg _) (inv_pos.mpr hz).le)
    _ = _ := by ring

/-- Along any sequence whose imaginary parts tend to infinity, z m_i tends to -1.
This is the asymptotic normalization needed for a probability representation;
it does not construct a measure or assert the existence of one. -/
theorem normalization_tendsto {zs : ℕ → ℂ} {ms : ℕ → ι → ℂ}
    (hS : ∀ i j, 0 ≤ S i j) (hz : ∀ k, 0 < (zs k).im)
    (hm : ∀ k, BasicEstimates.IsUpperSolution (ms k))
    (hsol : ∀ k, BasicEstimates.IsDysonSolution S a (zs k) (ms k))
    (hinfty : Tendsto (fun k => (zs k).im) atTop atTop) (i : ι) :
    Tendsto (fun k => zs k * ms k i) atTop (𝓝 (-1 : ℂ)) := by
  have hi : Tendsto (fun k => ((zs k).im)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hinfty
  have he : Tendsto (fun k => ‖zs k * ms k i + 1‖) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun k => normalization_error_bound hS (hz k) (hm k) (hsol k) i)
    simpa using (hi.const_mul |a i|).add ((hi.pow 2).const_mul (∑ j, S i j))
  have hzero : Tendsto (fun k => zs k * ms k i + 1) atTop (𝓝 (0 : ℂ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr he
  simpa using hzero.sub_const (1 : ℂ)
end NonSymmetricDyson.HighEnergy
