import Dyson.Full.Poisson
import Dyson.Full.BoundaryMeasure
import Dyson.Full.ExternalAlgebraic

/-! Removing the actual atomic part of a positive Stieltjes measure.
The new function is proved to be the transform of the remaining finite
positive measure; its Pick property is not an external hypothesis. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace NonSymmetricDyson.Full.Boundary
open ExternalAlgebraic

/-- Subtraction of the finitely many actual Stieltjes poles. -/
def atomRemoved (μ : Measure ℝ) (f : ℂ → ℂ) (A : Finset ℝ) (z : ℂ) : ℂ :=
  f z - ∑ τ ∈ A, ((μ {τ}).toReal : ℂ) / ((τ : ℂ)-z)

theorem remaining_measure_le (μ ν : Measure ℝ) (A : Finset ℝ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ) : ν ≤ μ := by
  rw [hdecomp]
  exact Measure.le_add_right le_rfl

theorem remaining_measure_finite (μ ν : Measure ℝ) [IsFiniteMeasure μ] (A : Finset ℝ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ) : IsFiniteMeasure ν :=
  isFiniteMeasure_of_le μ (remaining_measure_le μ ν A hdecomp)

/-- Exact transform of the finite atomic measure, proved by integration of
Dirac masses and finite sums. -/
theorem atomic_integral (μ ν : Measure ℝ) [IsFiniteMeasure μ] (A : Finset ℝ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ)
    (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ t, Poisson.resolvent (Poisson.point E η) t
      ∂(∑ τ ∈ A, μ {τ} • Measure.dirac τ)) =
      ∑ τ ∈ A, ((μ {τ}).toReal : ℂ) / ((τ : ℂ)-Poisson.point E η) := by
  have hm := Poisson.resolvent_integrable_of_height μ E hη
  have hsum : (∑ τ ∈ A, μ {τ} • Measure.dirac τ) ≤ μ := by
    exact (Measure.le_add_left (ν' := ν) le_rfl).trans_eq hdecomp.symm
  have heach : ∀ τ ∈ A, Integrable (Poisson.resolvent (Poisson.point E η))
      (μ {τ} • Measure.dirac τ) := by
    intro τ hτ
    apply hm.mono_measure
    exact (Finset.single_le_sum (fun τ _ => Measure.zero_le (μ {τ} • Measure.dirac τ)) hτ).trans hsum
  rw [integral_finset_sum_measure heach]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [integral_smul_measure, integral_dirac]
  simp [Poisson.resolvent, Algebra.smul_def, div_eq_mul_inv]

/-- The atom-subtracted function is the Stieltjes transform of the genuine
remaining positive measure, not an abstract new Pick function. -/
theorem atomRemoved_representation (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) (A : Finset ℝ) (hrep : Foundations.Represents f μ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ)
    (z : ℂ) (hz : z ∈ upper) :
    atomRemoved μ f A z = Poisson.stieltjes ν z := by
  have hm := Poisson.resolvent_integrable_of_height μ z.re (show 0 < z.im from hz)
  have hzpoint : Poisson.point z.re z.im = z := by apply Complex.ext <;> rfl
  rw [hzpoint] at hm
  have hν := hm.mono_measure (remaining_measure_le μ ν A hdecomp)
  have hsum : (∑ τ ∈ A, μ {τ} • Measure.dirac τ) ≤ μ := by
    exact (Measure.le_add_left (ν' := ν) le_rfl).trans_eq hdecomp.symm
  have hs := hm.mono_measure hsum
  have hi := integral_add_measure hν hs
  rw [← hdecomp] at hi
  have hatom := atomic_integral μ ν A hdecomp z.re (show 0 < z.im from hz)
  rw [hzpoint] at hatom
  rw [hatom] at hi
  unfold atomRemoved Poisson.stieltjes
  rw [hrep z hz]
  exact eq_sub_iff_add_eq.mpr hi.symm |>.symm

/-- A nonzero finite positive measure has a strictly positive imaginary
Stieltjes transform throughout the upper half-plane. -/
theorem positive_measure_stieltjes_pick (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≠ 0) (z : ℂ) (hz : z ∈ upper) :
    0 < (Poisson.stieltjes ν z).im := by
  have hzpoint : Poisson.point z.re z.im = z := by apply Complex.ext <;> rfl
  rw [← hzpoint, Poisson.stieltjes_im ν z.re (show 0 < z.im from hz)]
  apply (integral_pos_iff_support_of_nonneg
    (fun t => Poisson.kernel_nonneg (E := z.re) (t := t) (show 0 ≤ z.im from hz.le))
    (Poisson.kernel_integrable ν z.re (show 0 < z.im from hz))).mpr
  have hs : Function.support (Poisson.kernel z.re z.im) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    have hp : 0 < Poisson.kernel z.re z.im t := by
      unfold Poisson.kernel
      have hzim : 0 < z.im := hz
      exact div_pos hzim (by positivity)
    exact hp.ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr hν

theorem atomRemoved_zero_of_measure_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) (A : Finset ℝ) (hrep : Foundations.Represents f μ)
    (hdecomp : μ = 0 + ∑ τ ∈ A, μ {τ} • Measure.dirac τ) :
    ∀ z ∈ upper, atomRemoved μ f A z = 0 := by
  intro z hz
  rw [atomRemoved_representation μ 0 f A hrep hdecomp z hz]
  simp [Poisson.stieltjes]

theorem atomRemoved_pick_or_zero (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) (A : Finset ℝ) (hrep : Foundations.Represents f μ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ) :
    ν = 0 ∨ ∀ z ∈ upper, 0 < (atomRemoved μ f A z).im := by
  by_cases hν : ν = 0
  · exact Or.inl hν
  · letI := remaining_measure_finite μ ν A hdecomp
    exact Or.inr fun z hz => by
      rw [atomRemoved_representation μ ν f A hrep hdecomp z hz]
      exact positive_measure_stieltjes_pick ν hν z hz

theorem real_pole_denominator_ne_zero {τ : ℝ} {z : ℂ} (hz : z ∈ upper) :
    (τ : ℂ)-z ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp at hh
  exact (ne_of_gt hz) hh

/-- Finite rational subtraction preserves the actual analytic upper function. -/
theorem atomRemoved_analytic (μ : Measure ℝ) (f : ℂ → ℂ) (A : Finset ℝ)
    (hf : AnalyticOnNhd ℂ f upper) : AnalyticOnNhd ℂ (atomRemoved μ f A) upper := by
  intro z hz
  apply (hf z hz).sub
  apply A.analyticAt_fun_sum
  intro τ hτ
  exact analyticAt_const.div (analyticAt_const.sub analyticAt_id)
    (real_pole_denominator_ne_zero hz)

/-- At an atomless point, the scaled imaginary Stieltjes transform tends to
zero. This is proved directly by dominated convergence for a finite measure,
without assuming a probability normalization or a boundary inversion theorem. -/
theorem atomless_stieltjes_scaled_limit (ν : Measure ℝ) [IsFiniteMeasure ν]
    (τ : ℝ) (hτ : ν {τ} = 0) :
    Tendsto (fun η : ℝ => η * (Poisson.stieltjes ν (Poisson.point τ η)).im)
      (𝓝[>] 0) (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun η t => η ^ 2 / ((t-τ)^2+η^2)
  have hηevent : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hmeas : ∀ᶠ η : ℝ in 𝓝[>] 0, AEStronglyMeasurable (F η) ν := by
    filter_upwards [] with η
    exact ((measurable_const.div
      (((measurable_id.sub_const τ).pow_const 2).add_const (η^2)))).aestronglyMeasurable
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ᵐ t ∂ν, ‖F η t‖ ≤ (1 : ℝ) := by
    filter_upwards [hηevent] with η hη
    filter_upwards [] with t
    have hd : 0 < (t-τ)^2+η^2 := by positivity
    dsimp [F]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (t-τ)]
  have ht : ∀ᵐ t ∂ν, t ≠ τ := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (compl_mem_ae_iff.mpr hτ : {τ}ᶜ ∈ ae ν)
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun η => F η t) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [ht] with t ht
    have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hden : (t-τ)^2+(0:ℝ)^2 ≠ 0 := by
      simpa using pow_ne_zero 2 (sub_ne_zero.mpr ht)
    simpa [F] using (hid.pow 2).div (tendsto_const_nhds.add (hid.pow 2)) hden
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (f := fun _ : ℝ => (0 : ℝ)) (fun _ => (1 : ℝ)) hmeas hbound
    (integrable_const 1) hlim
  simp only [integral_zero] at hdct
  apply hdct.congr'
  filter_upwards [hηevent] with η hη
  rw [Poisson.stieltjes_im ν τ hη, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [F, Poisson.kernel]
  ring

/-- Actual atomic removal leaves no residual pole at an atomless point of the
remaining measure. -/
theorem atomRemoved_scaled_limit (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) (A : Finset ℝ) (hrep : Foundations.Represents f μ)
    (hdecomp : μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ)
    (τ : ℝ) (hτ : ν {τ} = 0) :
    Tendsto (fun η : ℝ => η * (atomRemoved μ f A (Poisson.point τ η)).im)
      (𝓝[>] 0) (𝓝 0) := by
  letI := remaining_measure_finite μ ν A hdecomp
  apply (atomless_stieltjes_scaled_limit ν τ hτ).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [atomRemoved_representation μ ν f A hrep hdecomp (Poisson.point τ η)
    (show 0 < η from hη)]

end NonSymmetricDyson.Full.Boundary
