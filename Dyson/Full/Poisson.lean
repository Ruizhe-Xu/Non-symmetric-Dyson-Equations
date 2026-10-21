import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Stieltjes and Poisson estimates for actual measures

These proofs retain the entire remote positive measure, including atoms.
No Dyson estimate is an external field or a hypothesis of itself.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NonSymmetricDyson.Full.Poisson

def point (E η : ℝ) : ℂ := ⟨E, η⟩
def resolvent (z : ℂ) (t : ℝ) : ℂ := ((t : ℂ) - z)⁻¹
def stieltjes (μ : Measure ℝ) (z : ℂ) : ℂ := ∫ t, resolvent z t ∂μ
def kernel (E η t : ℝ) : ℝ := η / ((t - E)^2 + η^2)

theorem measurable_resolvent (z : ℂ) : Measurable (resolvent z) := by
  unfold resolvent
  fun_prop

theorem real_gap_le_norm (E η t : ℝ) : |t-E| ≤ ‖(t : ℂ) - point E η‖ := by
  simpa [point] using Complex.abs_re_le_norm ((t : ℂ) - point E η)

theorem resolvent_norm_of_gap {E η t δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ |t-E|) : ‖resolvent (point E η) t‖ ≤ δ⁻¹ := by
  have h := hgap.trans (real_gap_le_norm E η t)
  simpa only [resolvent, norm_inv] using (inv_le_inv₀ (hδ.trans_le h) hδ).mpr h

theorem resolvent_integrable_of_gap (μ : Measure ℝ) [IsFiniteMeasure μ]
    {E η δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) :
    Integrable (resolvent (point E η)) μ := by
  apply (integrable_const (δ⁻¹)).mono' (measurable_resolvent _).aestronglyMeasurable
  exact hgap.mono fun t ht => resolvent_norm_of_gap hδ ht

/-- A probability Stieltjes transform is at most the reciprocal support distance,
uniformly at every height (including height zero). -/
theorem stieltjes_norm_of_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E η δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) :
    ‖stieltjes μ (point E η)‖ ≤ δ⁻¹ := by
  have h := norm_integral_le_of_norm_le_const
    (hgap.mono fun t ht => resolvent_norm_of_gap (η := η) hδ ht)
  simpa [stieltjes] using h

/-- The exact scalar resolvent identity; both denominators are nonzero by the
real support gap, so it also includes the real boundary value. -/
theorem resolvent_difference {E η t δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ |t-E|) :
    resolvent (point E η) t - resolvent (point E 0) t =
      (η : ℂ) * Complex.I *
        (resolvent (point E η) t * resolvent (point E 0) t) := by
  have hn (h : ℝ) : (t : ℂ) - point E h ≠ 0 := by
    apply norm_pos_iff.mp
    exact hδ.trans_le (hgap.trans (real_gap_le_norm E h t))
  unfold resolvent
  field_simp [hn η, hn 0]
  apply Complex.ext <;> simp [point] <;> ring

theorem resolvent_difference_norm {E η t δ : ℝ} (hδ : 0 < δ)
    (hη : 0 ≤ η) (hgap : δ ≤ |t-E|) :
    ‖resolvent (point E η) t - resolvent (point E 0) t‖ ≤ η * δ⁻¹^2 := by
  rw [resolvent_difference hδ hgap, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη,
    Complex.norm_I, mul_one]
  apply mul_le_mul_of_nonneg_left _ hη
  simpa only [pow_two] using mul_le_mul (resolvent_norm_of_gap (η := η) hδ hgap)
    (resolvent_norm_of_gap (η := 0) hδ hgap) (norm_nonneg _) (inv_nonneg.mpr hδ.le)

/-- Uniform O(η) approach to a real point at support distance δ, with the
explicit coefficient δ⁻² used in the off-support perturbation argument. -/
theorem stieltjes_difference_norm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E η δ : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) :
    ‖stieltjes μ (point E η) - stieltjes μ (point E 0)‖ ≤ η * δ⁻¹^2 := by
  unfold stieltjes
  rw [← integral_sub (resolvent_integrable_of_gap μ hδ hgap)
    (resolvent_integrable_of_gap μ hδ hgap)]
  have h := norm_integral_le_of_norm_le_const
    (hgap.mono fun t ht => resolvent_difference_norm hδ hη ht)
  simpa using h

theorem kernel_nonneg {E η t : ℝ} (hη : 0 ≤ η) : 0 ≤ kernel E η t := by
  exact div_nonneg hη (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem kernel_bound {E η t : ℝ} (hη : 0 < η) : kernel E η t ≤ η⁻¹ := by
  have hd : 0 < (t-E)^2 + η^2 := by positivity
  unfold kernel
  apply (div_le_iff₀ hd).mpr
  have h := sq_nonneg (t-E)
  field_simp
  nlinarith

theorem kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E : ℝ) {η : ℝ} (hη : 0 < η) : Integrable (kernel E η) μ := by
  apply (integrable_const (η⁻¹)).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold kernel
    fun_prop)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg hη.le)]
  exact kernel_bound hη

/-- Triangle separation from the local window. -/
theorem remote_separation {E τ r t : ℝ} (hE : |E-τ| ≤ r/2)
    (ht : r ≤ |t-τ|) : r/2 ≤ |t-E| := by
  have htriangle : |t-τ| ≤ |t-E| + |E-τ| := by
    convert abs_add_le (t-E) (E-τ) using 1 <;> ring
  linarith

theorem remote_kernel_bound {E τ r η t : ℝ} (hr : 0 < r) (hη : 0 ≤ η)
    (hE : |E-τ| ≤ r/2) (ht : r ≤ |t-τ|) :
    kernel E η t ≤ 4 * η / r^2 := by
  have hs := remote_separation hE ht
  have hd : 0 < (t-E)^2 + η^2 := by
    have : 0 < |t-E| := lt_of_lt_of_le (by positivity : 0 < r/2) hs
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (abs_pos.mp this)) (sq_nonneg _)
  have hsq : r^2 ≤ 4 * ((t-E)^2 + η^2) := by
    have := sq_nonneg (|t-E| - r/2)
    nlinarith [sq_abs (t-E), sq_nonneg η]
  unfold kernel
  apply (div_le_div_iff₀ hd (sq_pos_of_pos hr)).mpr
  nlinarith

/-- The full remote positive measure contributes at most 4η/r². No absolute
continuity is assumed, so this estimate also retains all remote atoms. -/
theorem remote_integral_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E τ r η : ℝ} (hr : 0 < r) (hη : 0 < η) (hE : |E-τ| ≤ r/2) :
    0 ≤ ∫ t in {t : ℝ | r ≤ |t-τ|}, kernel E η t ∂μ ∧
    (∫ t in {t : ℝ | r ≤ |t-τ|}, kernel E η t ∂μ) ≤ 4 * η / r^2 := by
  let A : Set ℝ := {t : ℝ | r ≤ |t-τ|}
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const (show Measurable (fun t : ℝ => |t-τ|) from
      (show Continuous (fun t : ℝ => |t-τ|) by fun_prop).measurable)
  constructor
  · exact integral_nonneg fun t => kernel_nonneg hη.le
  · have hi := (kernel_integrable μ E hη).integrableOn (s := A)
    have hb : ∀ᵐ t ∂μ.restrict A, kernel E η t ≤ 4 * η / r^2 := by
      filter_upwards [ae_restrict_mem hA] with t ht
      exact remote_kernel_bound hr hη.le hE ht
    calc
      _ ≤ ∫ _t in A, (4 * η / r^2) ∂μ := integral_mono_ae hi (integrable_const _) hb
      _ = μ.real A * (4 * η / r^2) := by simp [integral_const, smul_eq_mul]
      _ ≤ 4 * η / r^2 := by
        exact mul_le_of_le_one_left (by positivity) measureReal_le_one

/-- Local plus remote is the complete Poisson integral. -/
theorem poisson_split (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E τ r : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ t in {t : ℝ | |t-τ| < r}, kernel E η t ∂μ) +
      (∫ t in {t : ℝ | r ≤ |t-τ|}, kernel E η t ∂μ) =
      ∫ t, kernel E η t ∂μ := by
  have hm : MeasurableSet {t : ℝ | |t-τ| < r} := by
    exact measurableSet_lt (show Measurable (fun t : ℝ => |t-τ|) from
      (show Continuous (fun t : ℝ => |t-τ|) by fun_prop).measurable) measurable_const
  have hc : {t : ℝ | |t-τ| < r}ᶜ = {t : ℝ | r ≤ |t-τ|} := by
    ext t
    simp
  simpa only [hc] using integral_add_compl hm (kernel_integrable μ E hη)

/-- The positive real derivative weight outside the measure support. -/
def weight (μ : Measure ℝ) (E : ℝ) : ℝ := ∫ t, ((t-E)⁻¹)^2 ∂μ

theorem inverse_square_bound {x δ : ℝ} (hδ : 0 < δ) (hgap : δ ≤ |x|) :
    (x⁻¹)^2 ≤ (δ⁻¹)^2 := by
  have hi : |x|⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ (hδ.trans_le hgap) hδ).mpr hgap
  have hs := mul_self_le_mul_self (inv_nonneg.mpr (abs_nonneg x)) hi
  rw [← abs_inv] at hs
  simpa only [← pow_two, sq_abs] using hs

theorem weight_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {E δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) :
    Integrable (fun t : ℝ => ((t-E)⁻¹)^2) μ := by
  apply (integrable_const ((δ⁻¹)^2)).mono'
    (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [hgap] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((t-E)⁻¹))]
  exact inverse_square_bound hδ ht

/-- The derivative weight is bounded above and away from zero on a bounded
real region separated from a compactly supported probability measure. -/
theorem weight_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) (hfar : ∀ᵐ t ∂μ, |t-E| ≤ R) :
    (R⁻¹)^2 ≤ weight μ E ∧ weight μ E ≤ (δ⁻¹)^2 := by
  have hi := weight_integrable μ hδ hgap
  constructor
  · have hle : ∀ᵐ t ∂μ, (R⁻¹)^2 ≤ ((t-E)⁻¹)^2 := by
      filter_upwards [hgap, hfar] with t ht hf
      have hinv : R⁻¹ ≤ |t-E|⁻¹ := (inv_le_inv₀ hR (hδ.trans_le ht)).mpr hf
      have hs := mul_self_le_mul_self (inv_nonneg.mpr hR.le) hinv
      rw [← abs_inv] at hs
      simpa only [← pow_two, sq_abs] using hs
    simpa [weight] using integral_mono_ae (integrable_const ((R⁻¹)^2)) hi hle
  · have hle : ∀ᵐ t ∂μ, ((t-E)⁻¹)^2 ≤ (δ⁻¹)^2 :=
      hgap.mono fun t ht => inverse_square_bound hδ ht
    simpa [weight] using integral_mono_ae hi (integrable_const ((δ⁻¹)^2)) hle

theorem weight_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) (hfar : ∀ᵐ t ∂μ, |t-E| ≤ R) :
    0 < weight μ E :=
  lt_of_lt_of_le (sq_pos_of_pos (inv_pos.mpr hR)) (weight_bounds μ hδ hR hgap hfar).1

/-- Differentiation of the scalar resolvent, with the correct positive sign. -/
theorem hasDerivAt_resolvent {t : ℝ} {z : ℂ} (hne : (t : ℂ) - z ≠ 0) :
    HasDerivAt (fun w : ℂ => resolvent w t) (resolvent z t ^ 2) z := by
  have h := ((hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)).inv hne
  convert h using 1 <;> simp [resolvent, div_eq_mul_inv, inv_pow]

/-- A real support gap remains a complex gap in a uniform half-radius disk. -/
theorem complex_gap_in_ball {E δ t : ℝ} (hgap : δ ≤ |t-E|)
    {z : ℂ} (hz : z ∈ Metric.ball (point E 0) (δ/2)) :
    δ/2 ≤ ‖(t : ℂ) - z‖ := by
  have hz' : ‖z - point E 0‖ < δ/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have ht := hgap.trans (real_gap_le_norm E 0 t)
  have htriangle : ‖(t : ℂ) - point E 0‖ ≤
      ‖(t : ℂ) - z‖ + ‖z - point E 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

/-- Differentiation under the actual probability-measure integral at an
exterior real point. The dominating bound is proved on the whole local disk. -/
theorem hasDerivAt_stieltjes (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂μ, δ ≤ |t-E|) :
    HasDerivAt (stieltjes μ) (weight μ E : ℂ) (point E 0) := by
  have hh : 0 < δ/2 := by positivity
  have hn : ∀ᵐ (t : ℝ) ∂μ, ∀ (z : ℂ), z ∈ Metric.ball (point E 0) (δ/2) →
      δ/2 ≤ ‖(t : ℂ) - z‖ := hgap.mono fun t ht z hz => complex_gap_in_ball ht hz
  have hder : ∀ᵐ (t : ℝ) ∂μ, ∀ (z : ℂ), z ∈ Metric.ball (point E 0) (δ/2) →
      HasDerivAt (fun w : ℂ => resolvent w t) (resolvent z t ^ 2) z := by
    filter_upwards [hn] with t ht
    intro z hz
    exact hasDerivAt_resolvent (norm_pos_iff.mp (hh.trans_le (ht z hz)))
  have hbound : ∀ᵐ (t : ℝ) ∂μ, ∀ (z : ℂ), z ∈ Metric.ball (point E 0) (δ/2) →
      ‖resolvent z t ^ 2‖ ≤ ((δ/2)⁻¹)^2 := by
    filter_upwards [hn] with t ht
    intro z hz
    have hi : ‖resolvent z t‖ ≤ (δ/2)⁻¹ := by
      simpa [resolvent] using (inv_le_inv₀ (hh.trans_le (ht z hz)) hh).mpr (ht z hz)
    simpa [norm_pow, pow_two] using mul_self_le_mul_self (norm_nonneg _) hi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun z t => resolvent z t)
    (F' := fun z t => resolvent z t ^ 2) (bound := fun _ => ((δ/2)⁻¹)^2) hh
    (Filter.Eventually.of_forall fun z => (measurable_resolvent z).aestronglyMeasurable)
    (resolvent_integrable_of_gap μ hδ hgap)
    (by apply Measurable.aestronglyMeasurable; exact (measurable_resolvent _).pow_const 2)
    hbound (integrable_const _) hder
  have heq : (∫ t, resolvent (point E 0) t ^ 2 ∂μ) = (weight μ E : ℂ) := by
    rw [weight, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with t
    change (((t : ℂ) - (E : ℂ))⁻¹)^2 = ((((t-E)⁻¹)^2 : ℝ) : ℂ)
    norm_cast
  exact heq ▸ hd

/-- Positive height supplies a uniform denominator bound independently of the
real support. -/
theorem height_le_norm (E t : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    η ≤ ‖(t : ℂ) - point E η‖ := by
  have h := Complex.abs_im_le_norm ((t : ℂ) - point E η)
  simpa [point, abs_of_nonneg hη] using h

theorem resolvent_norm_of_height (E t : ℝ) {η : ℝ} (hη : 0 < η) :
    ‖resolvent (point E η) t‖ ≤ η⁻¹ := by
  have hn := height_le_norm E t hη.le
  simpa [resolvent] using (inv_le_inv₀ (hη.trans_le hn) hη).mpr hn

theorem resolvent_integrable_of_height (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E : ℝ) {η : ℝ} (hη : 0 < η) : Integrable (resolvent (point E η)) μ := by
  apply (integrable_const (η⁻¹)).mono' (measurable_resolvent _).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => resolvent_norm_of_height E t hη

theorem stieltjes_norm_of_height (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : ℝ) {η : ℝ} (hη : 0 < η) : ‖stieltjes μ (point E η)‖ ≤ η⁻¹ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := μ) (Filter.Eventually.of_forall fun t => resolvent_norm_of_height E t hη)
  simpa [stieltjes] using h

theorem resolvent_im (E η t : ℝ) : (resolvent (point E η) t).im = kernel E η t := by
  simp [resolvent, kernel, Complex.inv_im, Complex.normSq_apply, point, pow_two]

/-- The actual imaginary Stieltjes integral is the positive Poisson integral. -/
theorem stieltjes_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes μ (point E η)).im = ∫ t, kernel E η t ∂μ := by
  have h := integral_im (resolvent_integrable_of_height μ E hη)
  simpa only [RCLike.im_eq_complex_im, resolvent_im, stieltjes] using h.symm

/-- The complete Stieltjes imaginary part is local contribution plus a
nonnegative remote error with its explicit O(η) coefficient. -/
theorem local_remote_representation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E τ r η : ℝ} (hr : 0 < r) (hη : 0 < η) (hE : |E-τ| ≤ r/2) :
    ∃ error : ℝ, 0 ≤ error ∧ error ≤ 4 * η / r^2 ∧
      (stieltjes μ (point E η)).im =
        (∫ t in {t : ℝ | |t-τ| < r}, kernel E η t ∂μ) + error := by
  let error := ∫ t in {t : ℝ | r ≤ |t-τ|}, kernel E η t ∂μ
  have hb := remote_integral_bounds μ hr hη hE
  refine ⟨error, hb.1, hb.2, ?_⟩
  rw [stieltjes_im μ E hη]
  exact (poisson_split μ E τ r hη).symm

end NonSymmetricDyson.Full.Poisson
