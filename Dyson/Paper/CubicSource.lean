import Dyson.Paper.CubicConditional
import Dyson.Paper.SingularitiesSigns

/-! The conditional cubic proposition with the literal moving sign used in
the manuscript's coefficient premise. The same normalized center frame is
used in Θ and in every coefficient and error inequality. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.CubicSource
open Full Full.Singularities Full.PerronContinuation

section Uniform
variable {n : ℕ} (hn : 0<n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
variable (hτ : τ∉Boundary.singularUnion m)
variable (d : VaryingFrame S (Boundary.boundaryVector m)
  (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ)))
variable (hunit : ‖(WithLp.toLp 2 d.r₀ : EuclideanSpace ℝ (Fin n))‖=1)
variable (hbound : let p := fun z j => Real.sign (Boundary.boundaryVector m z j).re
  ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
    c≤(quadraticCoefficient (p z) (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
        (stableCoefficient (p z) (d.r z) (d.K z)) ∧
    (quadraticCoefficient (p z) (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
        (stableCoefficient (p z) (d.r z) (d.K z))≤C)

include hn algebraic puiseux hS hirr hupper heq hfront hτ hbound hunit

/-- Equality of actual signs translates the original local coefficient
premise into the fixed-sign analytic chart; no estimate is assumed here. -/
theorem fixed_sign_hypothesis :
    let p := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
  ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
    c≤(quadraticCoefficient p (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
        (stableCoefficient p (d.r z) (d.K z)) ∧
    (quadraticCoefficient p (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
        (stableCoefficient p (d.r z) (d.K z))≤C := by
  obtain ⟨c,C,hc,hC,hb⟩ := hbound
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hb,SingularitiesSigns.actual_frontier_signs hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ] with z hz hs
  simpa only [hs] using hz

theorem equation_of_uniform_nondegeneracy
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ:ℂ)),
    D.p=(fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) ∧
    D.r=d.r₀ ∧ D.l=d.l₀ ∧ ‖(WithLp.toLp 2 D.r : EuclideanSpace ℝ (Fin n))‖=1 ∧
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  exact CubicConditional.equation_of_uniform_nondegeneracy hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ d hunit
    (fixed_sign_hypothesis hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ d hunit hbound)
    normalForm imaginaryOrder

theorem holder_of_uniform_nondegeneracy
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple) :
    ∃ C ε : ℝ,0<C ∧ 0<ε ∧
      ∀ z∈ExternalAlgebraic.closedUpper,∀ w∈ExternalAlgebraic.closedUpper,
        ‖z-(τ:ℂ)‖<ε → ‖w-(τ:ℂ)‖<ε →
        ‖Boundary.boundaryVector m z-Boundary.boundaryVector m w‖≤C*‖z-w‖^((1:ℝ)/3) := by
  exact CubicConditional.holder_of_uniform_nondegeneracy hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ d hunit
    (fixed_sign_hypothesis hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ d hunit hbound)
    normalForm orientation

end Uniform

end NonSymmetricDyson.Paper.CubicSource
