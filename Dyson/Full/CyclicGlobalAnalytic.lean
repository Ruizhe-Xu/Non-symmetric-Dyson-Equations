import Dyson.Full.CyclicSemicircle

/-! Global holomorphy and quantitative normalization of the explicit scalar
semicircle branch. -/

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.CyclicGeneral
open CyclicExample (scalar)

theorem scalar_analytic_upper : AnalyticOnNhd ℂ scalar ExternalAlgebraic.upper := by
  have h := Boundary.family_coordinate_analytic (cycle 1) (fun _ => 0)
    (cycle_nonnegative 1) (canonical 1) (canonical_upper 1) (canonical_equation 1) 0
  apply AnalyticOnNhd.congr (isOpen_lt continuous_const Complex.continuous_im) h
  intro z hz
  exact congrFun (canonical_eq_scalar_global 1 hz) 0

theorem scalar_quadratic_normalization {z : ℂ} (hz : 0<z.im) :
    ‖z*scalar z+1‖ ≤ 4/‖z‖^2 := by
  have hm := scalar_norm_lt_one 1 hz (scalar_upper hz)
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz0
  have he : z*scalar z= -(scalar z^2+1) := by
    linear_combination CyclicExample.scalar_quadratic z
  have hb : ‖z‖*‖scalar z‖≤2 := by
    calc
      _ = ‖z*scalar z‖ := (norm_mul _ _).symm
      _ = ‖scalar z^2+1‖ := by rw [he, norm_neg]
      _ ≤ ‖scalar z‖^2+1 := by
        have hh := norm_add_le (scalar z^2) (1 : ℂ)
        rw [norm_pow, norm_one] at hh
        exact hh
      _ ≤ 2 := by nlinarith [norm_nonneg (scalar z)]
  have hmb : ‖scalar z‖≤2/‖z‖ := (le_div_iff₀ hn).mpr (by nlinarith)
  have hsq := (sq_le_sq₀ (norm_nonneg (scalar z)) (by positivity : (0 : ℝ)≤2/‖z‖)).mpr hmb
  have hid : z*scalar z+1= -(scalar z^2) := by
    linear_combination CyclicExample.scalar_quadratic z
  rw [hid, norm_neg, norm_pow]
  calc
    _ ≤ (2/‖z‖)^2 := hsq
    _ = _ := by ring

/-- Normalization holds along every upper-half-plane sequence escaping in
modulus, including horizontal tails. -/
theorem scalar_normalized_all_directions (zs : ℕ → ℂ)
    (hz : ∀ n, 0<(zs n).im) (hinfty : Tendsto (fun n => ‖zs n‖) atTop atTop) :
    Tendsto (fun n => zs n*scalar (zs n)) atTop (𝓝 (-1 : ℂ)) := by
  have hi : Tendsto (fun n => (‖zs n‖)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hinfty
  have hb : Tendsto (fun n => 4/‖zs n‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_eq_mul_inv, inv_pow] using (hi.pow 2).const_mul 4
  have hnorm : Tendsto (fun n => ‖zs n*scalar (zs n)+1‖) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => scalar_quadratic_normalization (hz n)) hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_neg_eq_add] using hnorm

end NonSymmetricDyson.Full.CyclicGeneral
