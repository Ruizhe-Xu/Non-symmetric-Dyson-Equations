import Mathlib
import Dyson.Full.Poisson

/-! Global tails and two-point Lipschitz estimates for arbitrary compactly
supported probability Stieltjes measures. Every estimate is proved from the
actual Bochner integral; there are no external assumptions in this module. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace NonSymmetricDyson.Full.StieltjesTails

open Poisson

theorem resolvent_norm_of_complex_gap {z : ℂ} {t δ : ℝ}
    (hδ : 0 < δ) (hgap : δ ≤ ‖(t : ℂ)-z‖) :
    ‖Poisson.resolvent z t‖ ≤ δ⁻¹ := by
  simpa [Poisson.resolvent] using (inv_le_inv₀ (hδ.trans_le hgap) hδ).mpr hgap

theorem integrable_of_complex_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ (t : ℝ) ∂μ, δ ≤ ‖(t : ℂ)-z‖) : Integrable (Poisson.resolvent z) μ := by
  apply (integrable_const (δ⁻¹)).mono' (measurable_resolvent z).aestronglyMeasurable
  exact hgap.mono fun t ht => resolvent_norm_of_complex_gap hδ ht

theorem resolvent_two_point {z w : ℂ} {t : ℝ}
    (hz : (t : ℂ)-z ≠ 0) (hw : (t : ℂ)-w ≠ 0) :
    Poisson.resolvent z t - Poisson.resolvent w t = (z-w) * Poisson.resolvent z t * Poisson.resolvent w t := by
  unfold Poisson.resolvent
  field_simp [hz, hw]
  ring

theorem stieltjes_lipschitz_of_complex_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z w : ℂ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hz : ∀ᵐ (t : ℝ) ∂μ, δ ≤ ‖(t : ℂ)-z‖)
    (hw : ∀ᵐ (t : ℝ) ∂μ, ε ≤ ‖(t : ℂ)-w‖) :
    ‖stieltjes μ z - stieltjes μ w‖ ≤ ‖z-w‖ * δ⁻¹ * ε⁻¹ := by
  unfold stieltjes
  rw [← integral_sub (integrable_of_complex_gap μ hδ hz)
    (integrable_of_complex_gap μ hε hw)]
  have hnorm : ∀ᵐ (t : ℝ) ∂μ,
      ‖Poisson.resolvent z t - Poisson.resolvent w t‖ ≤ ‖z-w‖ * δ⁻¹ * ε⁻¹ := by
    filter_upwards [hz, hw] with t hzt hwt
    rw [resolvent_two_point (norm_pos_iff.mp (hδ.trans_le hzt))
      (norm_pos_iff.mp (hε.trans_le hwt)), norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (resolvent_norm_of_complex_gap hδ hzt) (norm_nonneg _))
      (resolvent_norm_of_complex_gap hε hwt) (norm_nonneg _) (by positivity)
  simpa using norm_integral_le_of_norm_le_const hnorm

theorem stieltjes_upper_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z w : ℂ} (hz : 1 ≤ z.im) (hw : 1 ≤ w.im) :
    ‖stieltjes μ z - stieltjes μ w‖ ≤ ‖z-w‖ := by
  have hgap (v : ℂ) (hv : 1 ≤ v.im) : ∀ᵐ t : ℝ ∂μ, (1 : ℝ) ≤ ‖(t : ℂ)-v‖ := by
    filter_upwards [] with t
    have h := Complex.abs_im_le_norm ((t : ℂ)-v)
    have hv' : 0 ≤ v.im := by linarith
    exact hv.trans (by simpa [abs_of_nonneg hv'] using h)
  simpa using stieltjes_lipschitz_of_complex_gap μ (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<1) (hgap z hz) (hgap w hw)

theorem norm_denominator_bounds {z : ℂ} {t σ : ℝ} (ht : |t| ≤ σ) :
    ‖z‖-σ ≤ ‖(t : ℂ)-z‖ ∧ ‖(t : ℂ)-z‖ ≤ ‖z‖+σ := by
  constructor
  · have h := norm_sub_norm_le z (t : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev z (t : ℂ)] at h
    linarith
  · have h := norm_sub_le (t : ℂ) z
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    linarith

theorem ae_abs_le_of_support (μ : Measure ℝ) {σ : ℝ}
    (hμ : μ (Icc (-σ) σ)ᶜ = 0) : ∀ᵐ (t : ℝ) ∂μ, |t| ≤ σ := by
  have hm : Icc (-σ) σ ∈ ae μ := hμ
  exact Filter.Eventually.mono hm (fun t ht => abs_le.mpr ht)

theorem normalization_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z : ℂ} {σ : ℝ} (hz : σ < ‖z‖) (hs : ∀ᵐ (t : ℝ) ∂μ, |t| ≤ σ) :
    z * stieltjes μ z + 1 = ∫ t, (t : ℂ) * Poisson.resolvent z t ∂μ := by
  have hd : 0 < ‖z‖-σ := sub_pos.mpr hz
  have hg : ∀ᵐ (t : ℝ) ∂μ, ‖z‖-σ ≤ ‖(t : ℂ)-z‖ := hs.mono fun t ht =>
    (norm_denominator_bounds ht).1
  have hi := integrable_of_complex_gap μ hd hg
  calc
    _ = ∫ t, z * Poisson.resolvent z t + 1 ∂μ := by
      rw [integral_add (hi.const_mul z) (integrable_const _), integral_const_mul]
      simp [stieltjes]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hg] with t ht
      have hn := norm_pos_iff.mp (hd.trans_le ht)
      unfold Poisson.resolvent
      field_simp [hn]
      ring

theorem normalization_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z : ℂ} {σ : ℝ} (hσ : 0 ≤ σ) (hz : σ < ‖z‖)
    (hs : ∀ᵐ (t : ℝ) ∂μ, |t| ≤ σ) :
    ‖z * stieltjes μ z + 1‖ ≤ σ / (‖z‖-σ) := by
  rw [normalization_identity μ hz hs]
  have hd : 0 < ‖z‖-σ := sub_pos.mpr hz
  have hn : ∀ᵐ (t : ℝ) ∂μ, ‖(t : ℂ) * Poisson.resolvent z t‖ ≤ σ * (‖z‖-σ)⁻¹ := by
    filter_upwards [hs] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul ht (resolvent_norm_of_complex_gap hd (norm_denominator_bounds ht).1)
      (norm_nonneg _) hσ
  simpa [div_eq_mul_inv] using norm_integral_le_of_norm_le_const hn

theorem imaginary_tail_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E η σ : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hz : σ < ‖point E η‖)
    (hs : ∀ᵐ (t : ℝ) ∂μ, |t| ≤ σ) :
    η / (‖point E η‖+σ)^2 ≤ (stieltjes μ (point E η)).im ∧
    (stieltjes μ (point E η)).im ≤ η / (‖point E η‖-σ)^2 := by
  have hd : 0 < ‖point E η‖-σ := sub_pos.mpr hz
  have hbound : ∀ᵐ (t : ℝ) ∂μ,
      η / (‖point E η‖+σ)^2 ≤ kernel E η t ∧
      kernel E η t ≤ η / (‖point E η‖-σ)^2 := by
    filter_upwards [hs] with t ht
    obtain ⟨hlo, hhi⟩ := norm_denominator_bounds (z := point E η) ht
    have hn : 0 < ‖(t : ℂ)-point E η‖ := hd.trans_le hlo
    have heq : ‖(t : ℂ)-point E η‖^2 = (t-E)^2+η^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, point, pow_two]
    have hlosq := pow_le_pow_left₀ hd.le hlo 2
    have hhisq := pow_le_pow_left₀ (norm_nonneg _) hhi 2
    constructor
    · change η / (‖point E η‖+σ)^2 ≤ η / ((t-E)^2+η^2)
      rw [← heq]
      exact div_le_div_of_nonneg_left hη.le (sq_pos_of_pos hn) hhisq
    · change η / ((t-E)^2+η^2) ≤ η / (‖point E η‖-σ)^2
      rw [← heq]
      exact div_le_div_of_nonneg_left hη.le (sq_pos_of_pos hd) hlosq
  rw [stieltjes_im μ E hη]
  constructor
  · simpa using integral_mono_ae (integrable_const _) (kernel_integrable μ E hη)
      (hbound.mono fun t ht => ht.1)
  · simpa using integral_mono_ae (kernel_integrable μ E hη) (integrable_const _)
      (hbound.mono fun t ht => ht.2)

theorem stieltjes_real_tail_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z w : ℂ} {σ : ℝ} (hs : ∀ᵐ (t : ℝ) ∂μ, |t| ≤ σ)
    (hz : σ+1 ≤ |z.re|) (hw : σ+1 ≤ |w.re|) :
    ‖stieltjes μ z - stieltjes μ w‖ ≤ ‖z-w‖ := by
  have hgap (v : ℂ) (hv : σ+1 ≤ |v.re|) : ∀ᵐ (t : ℝ) ∂μ, (1 : ℝ) ≤ ‖(t : ℂ)-v‖ := by
    filter_upwards [hs] with t ht
    have htri : |v.re| ≤ |t| + |t-v.re| := by
      have h := abs_add_le t (v.re-t)
      simpa [abs_sub_comm, add_comm] using h
    have hn := Complex.abs_re_le_norm ((t : ℂ)-v)
    simp only [Complex.sub_re, Complex.ofReal_re] at hn
    linarith
  simpa using stieltjes_lipschitz_of_complex_gap μ (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<1) (hgap z hz) (hgap w hw)

end NonSymmetricDyson.Full.StieltjesTails
