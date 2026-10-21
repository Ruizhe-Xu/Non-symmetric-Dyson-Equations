import Dyson.Paper.Cubic
import Dyson.Paper.SingularitiesNormalization

/-! Literal cubic proposition with the same Euclidean-unit Perron vector
used in Θ, σ, ψ, the stable coefficient, and every displayed error bound. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.CubicNormalized
open Full Full.Singularities

theorem equation_symmetric
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    (∑ j,D.r j^2=1) ∧
    ‖(WithLp.toLp 2 D.r : EuclideanSpace ℝ (Fin n))‖=1 ∧
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
  obtain ⟨r,l,hd,hsq,hunit⟩ := SingularitiesNormalization.normalized_frontier_perron
    perron hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  obtain ⟨D,_,hr,_⟩ := SingularitiesFrontier.data_with_perron_symmetric
    hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ r l hd
  refine ⟨D,?_,?_,Cubic.equation_with_perron_data normalForm imaginaryOrder hn
    algebraic puiseux S a hS m hupper heq τ hτ D⟩
  · simpa only [hr] using hsq
  · simpa only [hr] using hunit


theorem equation_nonbacktracking
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀ i j,S i j=G.matrix (e i) (e j))
    (hpot : ∀ i,a i=av (G.head (e i)))
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    (∑ j,D.r j^2=1) ∧
    ‖(WithLp.toLp 2 D.r : EuclideanSpace ℝ (Fin n))‖=1 ∧
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
  obtain ⟨r,l,hd,hsq,hunit⟩ := SingularitiesNormalization.normalized_frontier_perron
    perron hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  obtain ⟨D,_,hr,_⟩ := SingularitiesFrontier.data_with_perron_nonbacktracking
    hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ r l hd
  refine ⟨D,?_,?_,Cubic.equation_with_perron_data normalForm imaginaryOrder hn
    algebraic puiseux S a hS m hupper heq τ hτ D⟩
  · simpa only [hr] using hsq
  · simpa only [hr] using hunit



end NonSymmetricDyson.Paper.CubicNormalized
