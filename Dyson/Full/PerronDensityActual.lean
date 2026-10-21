import Dyson.Full.PerronDensityComparison
import Dyson.Full.MainSpectral

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.PerronContinuation
open Singularities SingularSpectral ExternalAlgebraic

/-- δ is comparable with the manuscript's total density ρ on an actual
closed upper half-disc, including both real sides of a regular frontier. -/
theorem actual_frame_density_comparison {n : ℕ} [Nonempty (Fin n)]
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m)
    (d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) :
    ∃ ε c C : ℝ,0<ε ∧ 0<c ∧ 0<C ∧ ∀ z : ℂ,0≤z.im → ‖z-(τ:ℂ)‖≤ε →
      c*(∑ i,(Boundary.boundaryVector m z i).im)≤perronDensity (d.l z) (Boundary.boundaryVector m z) ∧
      perronDensity (d.l z) (Boundary.boundaryVector m z)≤C*(∑ i,(Boundary.boundaryVector m z i).im) := by
  obtain ⟨c,C,hc,hC,hcompare⟩ := d.density_comparison
    (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
    (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  have hactual := regular_closed_upper_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hbound : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      c*(∑ i,(Boundary.boundaryVector m z i).im)≤perronDensity (d.l z) (Boundary.boundaryVector m z) ∧
      perronDensity (d.l z) (Boundary.boundaryVector m z)≤C*(∑ i,(Boundary.boundaryVector m z i).im) := by
    filter_upwards [hcompare,hactual] with z hz ha
    apply hz
    intro i
    have hh := mul_nonneg (ha.2.2.1 i) (norm_nonneg (Boundary.boundaryVector m z i))
    simpa [normalizedImag,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (ha.1 i))] using hh
  obtain ⟨ε,hε,he⟩ := closed_upper_eventual_radius τ _ hbound
  exact ⟨ε,c,C,hε,hc,hC,he⟩

/-- Full actual-model instantiation of the Perron-density comparison. -/
theorem regular_frontier_density_comparison
    (external : ExternalContinuousPerron) {n : ℕ} (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ)),
    ∃ ε c C : ℝ,0<ε ∧ 0<c ∧ 0<C ∧ ∀ z : ℂ,0≤z.im → ‖z-(τ:ℂ)‖≤ε →
      c*(∑ i,(Boundary.boundaryVector m z i).im)≤perronDensity (d.l z) (Boundary.boundaryVector m z) ∧
      perronDensity (d.l z) (Boundary.boundaryVector m z)≤C*(∑ i,(Boundary.boundaryVector m z i).im) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨d⟩ := regular_frontier_varying_frame external hn algebraic puiseux
    S a hS hirr m hupper heq τ i hfront hτ
  exact ⟨d,actual_frame_density_comparison algebraic puiseux S a hS m hupper heq τ hτ d⟩

end NonSymmetricDyson.Full.PerronContinuation
