import Dyson.Full.ExtendedDensity
import Dyson.Full.AtomRemoval

/-! The manuscript's pointwise density convention, including the finite
exceptional set: remove exactly the actual atomic poles, then take the
extended imaginary boundary limit. All measure and positivity properties
of this subtraction are proved from the actual measure decomposition. -/

noncomputable section
open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryMeasure Foundations

/-- Density continuity holds on the complement of each coordinate's own
singular set, not only on the complement of their union. -/
theorem family_coordinate_density_continuous {ι : Type*} [Fintype ι]
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i : ι) :
    ContinuousOn (realDensity m i) (singularSet (fun z => m z i))ᶜ := by
  have hc := (algebraic_continuous_extension puiseux (fun z => m z i)
    (family_coordinate_analytic S a hS m hupper heq i)
    (solution_algebraic algebraic S a hS m hupper heq i)
    (fun z hz => hupper z hz i)).1
  have hr := hc.comp Complex.continuous_ofReal.continuousOn
    (show MapsTo Complex.ofReal (singularSet (fun z => m z i))ᶜ
      (regularDomain (fun z => m z i)) from fun x hx => Or.inr ⟨x, hx, rfl⟩)
  exact (Complex.continuous_im.comp_continuousOn hr).div_const Real.pi

/-- Complete pointwise density statement. The finite set is the actual
singular set, all coefficients are actual singleton masses, and the new
density is defined by actual extended boundary limits even at poles.
Zero weights in the finite atomic sum are harmless. -/
theorem pole_removed_density_decomposition {ι : Type*} [Fintype ι]
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (rational : RationalAlgebraicity) (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i)) (i : ι) :
    ∃ A : Finset ℝ, (A : Set ℝ) = singularSet (fun z => m z i) ∧
      let h := atomRemoved (μ i) (fun z => m z i) A
      (∀ x : ℝ, Tendsto (fun η => ENNReal.ofReal ((h (vertical x η)).im / Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 (extendedDensity h x))) ∧
      (∀ x ∉ A, extendedDensity h x = ENNReal.ofReal (realDensity m i x)) ∧
      ContinuousOn (extendedDensity h) (A : Set ℝ)ᶜ ∧
      μ i = volume.withDensity (extendedDensity h) +
        ∑ τ ∈ A, μ i {τ} • Measure.dirac τ ∧
      (∀ x : ℝ, Tendsto (fun η => η * (h (vertical x η)).im)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) ∧
      (∀ (x : ℝ) (p : PuiseuxChart h x), -1 < (p.exponent : ℝ) / p.denominator) := by
  classical
  letI := hμ i
  obtain ⟨A, hA, hdecomp⟩ := family_measure_decomposition algebraic puiseux inversion
    S a hS m hupper heq μ hμ hrep i
  let f : ℂ → ℂ := fun z => m z i
  let F : ℂ → ℂ := fun z => boundaryVector m z i
  let ν : Measure ℝ := densityMeasure F
  let h : ℂ → ℂ := atomRemoved (μ i) f A
  have hsplit : μ i = ν + ∑ τ ∈ A, μ i {τ} • Measure.dirac τ := hdecomp
  have ha : AnalyticOnNhd ℂ f upper := family_coordinate_analytic S a hS m hupper heq i
  have halg : AlgebraicOnUpper f := solution_algebraic algebraic S a hS m hupper heq i
  have hha : AnalyticOnNhd ℂ h upper := atomRemoved_analytic (μ i) f A ha
  have hhalg : AlgebraicOnUpper h :=
    rational.subtract f A (fun τ => ((μ i {τ}).toReal : ℂ)) halg
  have hpick : (∀ z ∈ upper, h z = 0) ∨ (∀ z ∈ upper, 0 < (h z).im) := by
    rcases atomRemoved_pick_or_zero (μ i) ν f A (hrep i) hsplit with hz | hp
    · left
      exact atomRemoved_zero_of_measure_zero (μ i) f A (hrep i) (by simpa [hz] using hsplit)
    · exact Or.inr hp
  have hreg : ∀ x ∉ A, extendedDensity h x = ENNReal.ofReal (realDensity m i x) := by
    intro x hx
    have hxs : x ∉ singularSet f := by simpa [f, ← hA] using hx
    have hb := (algebraic_continuous_extension puiseux f ha halg
      (fun z hz => hupper z hz i)).2.2 x hxs
    exact extendedDensity_sub_poles_regular f A (fun τ => (μ i {τ}).toReal) x hx (F x) hb
  have hae : extendedDensity h =ᵐ[volume] (fun x => ENNReal.ofReal (realDensity m i x)) := by
    filter_upwards [A.finite_toSet.countable.ae_notMem (μ := (volume : Measure ℝ))] with x hx
    exact hreg x hx
  have hzero : ∀ x : ℝ, Tendsto (fun η => η * (h (vertical x η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    intro x
    have hp : ∀ η : ℝ, Poisson.point x η = vertical x η := by
      intro η
      apply Complex.ext <;> simp [Poisson.point, vertical]
    simpa only [hp] using
      atomRemoved_scaled_limit (μ i) ν f A (hrep i) hsplit x (measure_singleton x)
  refine ⟨A, hA, ?_⟩
  change (∀ x, _) ∧ (∀ x ∉ A, _) ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨fun x => algebraic_extended_density_limit puiseux h hha hhalg hpick x,
    hreg, ?_, ?_, hzero, ?_⟩
  · have hc := ENNReal.continuous_ofReal.comp_continuousOn
      (family_coordinate_density_continuous algebraic puiseux S a hS m hupper heq i)
    rw [← hA] at hc
    apply hc.congr
    intro x hx
    exact hreg x hx
  · rw [withDensity_congr_ae hae]
    exact hdecomp
  · intro x p
    apply PuiseuxChart.exponent_gt_neg_one_of_zero_atom_limit p _ (hzero x)
    intro z hz
    change 0 ≤ (h z).im
    rcases hpick with hp | hp
    · rw [hp z hz]
      simp
    · exact (hp z hz).le

end NonSymmetricDyson.Full.Boundary
