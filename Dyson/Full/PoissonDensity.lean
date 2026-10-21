import Dyson.Full.PoissonScales

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace NonSymmetricDyson.Full.Poisson

/-- Local density identity for actual measures. The density domain B may be
one-sided even though the local window A is symmetric. -/
theorem local_density_integral (μ : Measure ℝ) (A B : Set ℝ) (v : ℝ → ℝ)
    (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hμ : μ.restrict A = (volume.restrict B).withDensity (fun x => ENNReal.ofReal (v x)))
    (E η : ℝ) :
    (∫ x in A, kernel E η x ∂μ) = ∫ x in B, kernel E η x * v x := by
  rw [hμ, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun x => ENNReal.ofReal (v x)))
    (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top) (kernel E η)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hn x), smul_eq_mul, mul_comm]

theorem density_kernel_integrable {α η C E : ℝ} {A : Set ℝ} {v : ℝ → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) (hC : 0 ≤ C)
    (hA : MeasurableSet A) (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hu : ∀ x ∈ A, v x ≤ C*|x|^α) :
    IntegrableOn (fun x => kernel E η x * v x) A := by
  have hd := ((weighted_kernel_integrable E hα hα1 hη).const_mul C).integrableOn (s := A)
  apply hd.mono' (by apply Measurable.aestronglyMeasurable; unfold kernel; fun_prop)
  filter_upwards [ae_restrict_mem hA] with x hx
  have hk := kernel_nonneg (E := E) (t := x) hη.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (hn x))]
  have h := mul_le_mul_of_nonneg_left (hu x hx) hk
  nlinarith

/-- Pointwise density comparisons become comparisons with the proved model
integrals, using Lebesgue integration rather than an assumed scalar bound. -/
theorem density_kernel_comparison {α η c C E : ℝ} {A : Set ℝ} {v : ℝ → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hA : MeasurableSet A) (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hl : ∀ x ∈ A, c*|x|^α ≤ v x) (hu : ∀ x ∈ A, v x ≤ C*|x|^α) :
    c*(∫ x in A, kernel E η x * |x|^α) ≤ ∫ x in A, kernel E η x * v x ∧
    (∫ x in A, kernel E η x * v x) ≤ C*(∫ x in A, kernel E η x * |x|^α) := by
  have hi := density_kernel_integrable hα hα1 hη hC hA hv hn hu (E := E)
  have hm := (weighted_kernel_integrable E hα hα1 hη).integrableOn (s := A)
  constructor
  · rw [← integral_const_mul]
    apply setIntegral_mono_on (hm.const_mul c) hi hA
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hl x hx) (kernel_nonneg (E := E) (t := x) hη.le)
    nlinarith
  · rw [← integral_const_mul]
    apply setIntegral_mono_on hi (hm.const_mul C) hA
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hu x hx) (kernel_nonneg (E := E) (t := x) hη.le)
    nlinarith

theorem symmetric_window_eq (r : ℝ) : {x : ℝ | |x-(0:ℝ)| < r} = Ioo (-r) r := by
  ext x
  simp [abs_lt]

/-- Complete local cusp Poisson estimate for a probability measure, including
all remote atoms. At α=1/3 this is precisely the cusp scale q^(1/3). -/
theorem cusp_measure_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {α c C r E η : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hr : 0 < r) (hη : 0 < η) (hsmall : |E|+η < r/8) (hq1 : |E|+η ≤ 1)
    (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hl : ∀ x ∈ Ioo (-r) r, c*|x|^α ≤ v x)
    (hu : ∀ x ∈ Ioo (-r) r, v x ≤ C*|x|^α)
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/5)*(|E|+η)^α ≤ (stieltjes μ (point E η)).im ∧
    (stieltjes μ (point E η)).im ≤
      (C*(Real.pi+fractionalMoment α)+4/r^2) * (|E|+η)^α := by
  have hE : |E-(0:ℝ)| ≤ r/2 := by simpa using (show |E| ≤ r/2 by linarith)
  obtain ⟨error, he0, he, heq⟩ := local_remote_representation μ hr hη hE
  rw [symmetric_window_eq, local_density_integral μ _ _ v hv hn hμ] at heq
  have hcomp := density_kernel_comparison hα hα1 hη hc hC measurableSet_Ioo hv hn hl hu (E := E)
  have hlo := cusp_lower hα hα1 hη (by linarith [abs_nonneg E] : |E|+2*η < r)
  have hup := local_weighted_kernel_upper E (Ioo (-r) r) hα hα1 hη
  have hqpow : η ≤ (|E|+η)^α :=
    (le_add_of_nonneg_left (abs_nonneg E)).trans
      (Real.self_le_rpow_of_le_one (by positivity) hq1 hα1.le)
  have herr : error ≤ (4/r^2)*(|E|+η)^α := by
    have h := mul_le_mul_of_nonneg_left hqpow (by positivity : 0 ≤ 4/r^2)
    calc error ≤ 4*η/r^2 := he
         _ ≤ (4/r^2)*(|E|+η)^α := by
           convert h using 1 <;> ring
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hc]
  · nlinarith [mul_le_mul_of_nonneg_left hup hC]

/-- Complete support-side edge Poisson estimate for an actual local one-sided
measure density. At α=1/2 the scale is sqrt(κ+η). -/
theorem edge_support_measure_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {α c C r κ η : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hr : 0 < r) (hκ : 0 ≤ κ) (hη : 0 < η) (hsmall : κ+η < r/8) (hq1 : κ+η ≤ 1)
    (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hl : ∀ x ∈ Ioo 0 r, c*|x|^α ≤ v x)
    (hu : ∀ x ∈ Ioo 0 r, v x ≤ C*|x|^α)
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/5)*(κ+η)^α ≤ (stieltjes μ (point κ η)).im ∧
    (stieltjes μ (point κ η)).im ≤
      (C*(Real.pi+fractionalMoment α)+4/r^2) * (κ+η)^α := by
  have hE : |κ-(0:ℝ)| ≤ r/2 := by rw [sub_zero, abs_of_nonneg hκ]; linarith
  obtain ⟨error, he0, he, heq⟩ := local_remote_representation μ hr hη hE
  rw [symmetric_window_eq, local_density_integral μ _ _ v hv hn hμ] at heq
  have hcomp := density_kernel_comparison hα hα1 hη hc hC measurableSet_Ioo hv hn hl hu (E := κ)
  have hlo := edge_support_lower hα hα1 hκ hη (by linarith : κ+2*η < r)
  have hup := local_weighted_kernel_upper κ (Ioo 0 r) hα hα1 hη
  rw [abs_of_nonneg hκ] at hup
  have hqpow : η ≤ (κ+η)^α :=
    (le_add_of_nonneg_left hκ).trans
      (Real.self_le_rpow_of_le_one (by positivity) hq1 hα1.le)
  have herr : error ≤ (4/r^2)*(κ+η)^α := by
    have h := mul_le_mul_of_nonneg_left hqpow (by positivity : 0 ≤ 4/r^2)
    calc error ≤ 4*η/r^2 := he
         _ ≤ (4/r^2)*(κ+η)^α := by
           convert h using 1 <;> ring
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hc]
  · nlinarith [mul_le_mul_of_nonneg_left hup hC]

/-- Complete gap-side edge estimate, with the remote measure absorbed in the
same η q^(α-1) scale. At α=1/2 this is η/sqrt(κ+η). -/
theorem edge_gap_measure_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {α c C r κ η : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hr : 0 < r) (hκ : 0 ≤ κ) (hη : 0 < η) (hsmall : κ+η < r/8) (hq1 : κ+η ≤ 1)
    (hv : Measurable v) (hn : ∀ x, 0 ≤ v x)
    (hl : ∀ x ∈ Ioo 0 r, c*|x|^α ≤ v x)
    (hu : ∀ x ∈ Ioo 0 r, v x ≤ C*|x|^α)
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/10)*(η*((κ+η)^α/(κ+η))) ≤ (stieltjes μ (point (-κ) η)).im ∧
    (stieltjes μ (point (-κ) η)).im ≤
      (2*C*gapMoment α+4/r^2) * (η*((κ+η)^α/(κ+η))) := by
  have hq : 0 < κ+η := by positivity
  have hE : |-κ-(0:ℝ)| ≤ r/2 := by rw [sub_zero, abs_neg, abs_of_nonneg hκ]; linarith
  obtain ⟨error, he0, he, heq⟩ := local_remote_representation μ hr hη hE
  rw [symmetric_window_eq, local_density_integral μ _ _ v hv hn hμ] at heq
  have hcomp := density_kernel_comparison hα hα1 hη hc hC measurableSet_Ioo hv hn hl hu (E := -κ)
  have hlo := edge_gap_lower hα hα1 hκ hη (by linarith : 2*(κ+η) < r)
  have hup := edge_gap_upper (r := r) hα hα1 hκ hη
  have hqpow : 1 ≤ (κ+η)^α/(κ+η) := by
    apply (le_div_iff₀ hq).mpr
    simpa using Real.self_le_rpow_of_le_one hq.le hq1 hα1.le
  have herr : error ≤ (4/r^2)*(η*((κ+η)^α/(κ+η))) := by
    have h := mul_le_mul_of_nonneg_left hqpow hη.le
    have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 4/r^2)
    calc error ≤ 4*η/r^2 := he
         _ ≤ (4/r^2)*(η*((κ+η)^α/(κ+η))) := by
           convert hh using 1 <;> ring
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hc]
  · nlinarith [mul_le_mul_of_nonneg_left hup hC]

/-- Recenter a genuine probability measure at the singular energy τ. -/
def recenter (μ : Measure ℝ) (τ : ℝ) : Measure ℝ := μ.map (fun t => t-τ)

theorem recenter_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (τ : ℝ) :
    IsProbabilityMeasure (recenter μ τ) := by
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- Exact translation identity extends the proved local scales from a centered
window to an arbitrary edge/cusp energy without changing the measure mass. -/
theorem stieltjes_recenter (μ : Measure ℝ) (τ E η : ℝ) :
    stieltjes (recenter μ τ) (point E η) = stieltjes μ (point (E+τ) η) := by
  unfold recenter stieltjes
  rw [integral_map (by fun_prop : AEMeasurable (fun t : ℝ => t-τ) μ)
    (measurable_resolvent _).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold resolvent
  congr 1
  apply Complex.ext <;> simp [point] <;> ring

/-- The half-power gap scale is exactly η/sqrt(q), with no asymptotic notation. -/
theorem half_gap_scale (η q : ℝ) : η*(q^(1/(2:ℝ))/q) = η/Real.sqrt q := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div_self']
  ring

/-- Reflection changes a left edge into the right-edge convention used above. -/
def reflectMeasure (μ : Measure ℝ) : Measure ℝ := μ.map Neg.neg

theorem reflect_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (reflectMeasure μ) := by
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- Reflection preserves the Poisson imaginary part after reflecting E.
Together with recentering this covers both orientations of every edge. -/
theorem stieltjes_reflect_im (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (stieltjes (reflectMeasure μ) (point E η)).im =
      (stieltjes μ (point (-E) η)).im := by
  letI := reflect_probability μ
  rw [stieltjes_im _ _ hη, stieltjes_im _ _ hη]
  unfold reflectMeasure
  rw [integral_map (by fun_prop : AEMeasurable (Neg.neg : ℝ → ℝ) μ)
    (by apply Measurable.aestronglyMeasurable; unfold kernel; fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold kernel
  congr 1
  ring

end NonSymmetricDyson.Full.Poisson
