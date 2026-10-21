import Dyson.Full.Poisson
import Dyson.Full.MainBoundary

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NonSymmetricDyson.Full.Boundary
open ExternalAlgebraic

/-- A compactly supported measure has the claimed almost-everywhere real gap. -/
theorem exterior_ae_gap (μ : Measure ℝ) {σ τ : ℝ}
    (hs : μ (Icc (-σ) σ)ᶜ = 0) :
    ∀ᵐ t ∂μ, |τ|-σ ≤ |t-τ| := by
  have hm : Icc (-σ) σ ∈ ae μ := hs
  filter_upwards [hm] with t ht
  have ht' : |t| ≤ σ := abs_le.mpr ht
  have h := abs_sub_abs_le_abs_sub τ t
  rw [abs_sub_comm τ t] at h
  linarith

theorem point_eq_vertical (τ η : ℝ) : Poisson.point τ η = vertical τ η := by
  apply Complex.ext <;> simp [Poisson.point, vertical]

/-- The actual Stieltjes transform is continuous at every exterior real point,
with a finite limit from the whole upper half-plane. -/
theorem exterior_upper_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) {σ τ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0)
    (hτ : σ < |τ|) (hrep : Foundations.Represents f μ) :
    Tendsto f (𝓝[upper] (τ : ℂ)) (𝓝 (Poisson.stieltjes μ (Poisson.point τ 0))) := by
  have hc := (Poisson.hasDerivAt_stieltjes μ (sub_pos.mpr hτ) (exterior_ae_gap μ hs)).continuousAt
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hrep z hz).symm

/-- Outside the compact support, the boundary Stieltjes integral is real. -/
theorem exterior_stieltjes_im_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {σ τ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0) (hτ : σ < |τ|) :
    (Poisson.stieltjes μ (Poisson.point τ 0)).im = 0 := by
  have hi := Poisson.resolvent_integrable_of_gap μ (η := 0) (sub_pos.mpr hτ) (exterior_ae_gap μ hs)
  have h := integral_im hi
  simpa [RCLike.im_eq_complex_im, Poisson.resolvent_im, Poisson.kernel,
    Poisson.stieltjes] using h.symm

/-- The canonical boundary extension agrees with the real exterior integral;
no arbitrary value of extendFrom is used. -/
theorem exterior_boundary_value (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) {σ τ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0)
    (hτ : σ < |τ|) (hrep : Foundations.Represents f μ) :
    boundaryExtension f (τ : ℂ) = Poisson.stieltjes μ (Poisson.point τ 0) :=
  extendFrom_eq (real_mem_closure_upper τ) (exterior_upper_limit μ f hs hτ hrep)

theorem exterior_boundary_im_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) {σ τ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0)
    (hτ : σ < |τ|) (hrep : Foundations.Represents f μ) :
    (boundaryExtension f (τ : ℂ)).im = 0 := by
  rw [exterior_boundary_value μ f hs hτ hrep]
  exact exterior_stieltjes_im_zero μ hs hτ

/-- Compact support excludes all divergent vertical boundary points outside
its containing interval. This does not require a Puiseux assumption. -/
theorem exterior_not_singular (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) {σ τ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0)
    (hτ : σ < |τ|) (hrep : Foundations.Represents f μ) :
    τ ∉ singularSet f := by
  apply not_singular_of_bounded (M := (|τ|-σ)⁻¹)
  intro η hη
  have heq : f (vertical τ η) = Poisson.stieltjes μ (Poisson.point τ η) := by
    rw [point_eq_vertical]
    exact hrep _ (by simpa using hη)
  rw [heq]
  exact Poisson.stieltjes_norm_of_gap μ (sub_pos.mpr hτ) (exterior_ae_gap μ hs)

theorem singularSet_subset_support_interval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) {σ : ℝ} (hs : μ (Icc (-σ) σ)ᶜ = 0)
    (hrep : Foundations.Represents f μ) : singularSet f ⊆ Icc (-σ) σ := by
  intro τ hτ
  apply abs_le.mp
  by_contra h
  exact exterior_not_singular μ f hs (lt_of_not_ge h) hrep hτ

/-- Positive regular density is supported in the same compact interval as the
representing measures, uniformly over the finite family. -/
theorem regularSupport_subset_support_interval {ι : Type*} [Fintype ι]
    (m : ℂ → ι → ℂ) (μ : ι → Measure ℝ) (σ : ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hs : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i)) (i : ι) :
    regularSupport m i ⊆ Icc (-σ) σ := by
  intro τ hτ
  apply abs_le.mp
  by_contra h
  letI := hμ i
  have hz := exterior_boundary_im_zero (μ i) (fun z => m z i) (hs i) (lt_of_not_ge h) (hrep i)
  have hp := hτ.2
  change 0 < (boundaryExtension (fun z => m z i) (τ : ℂ)).im at hp
  rw [hz] at hp
  exact lt_irrefl _ hp

theorem singularUnion_subset_support_interval {ι : Type*} [Fintype ι]
    (m : ℂ → ι → ℂ) (μ : ι → Measure ℝ) (σ : ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hs : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i)) :
    singularUnion m ⊆ Icc (-σ) σ := by
  intro τ hτ
  obtain ⟨i, hi⟩ := mem_iUnion.mp hτ
  letI := hμ i
  exact singularSet_subset_support_interval (μ i) (fun z => m z i) (hs i) (hrep i) hi

end NonSymmetricDyson.Full.Boundary
