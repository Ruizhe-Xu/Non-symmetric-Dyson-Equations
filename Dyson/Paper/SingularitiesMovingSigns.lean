import Dyson.Paper.SingularitiesSigns

/-! Proposition psi-positive-and-nondegenerate with the manuscript's literal
moving p(z)=sign(Re m(z)). The fixed sign in the local chart is proved equal
to this function throughout the relevant neighborhood. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.SingularitiesMovingSigns
open Full Full.Singularities Full.PerronContinuation
variable {n : ℕ}

theorem uniform_nondegeneracy_symmetric
    (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) :
    let p := fun z j => Real.sign (Boundary.boundaryVector m z j).re
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
      c≤(quadraticCoefficient (p z) (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
          (stableCoefficient (p z) (d.r z) (d.K z)) ∧
      (quadraticCoefficient (p z) (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
          (stableCoefficient (p z) (d.r z) (d.K z))≤C := by
  obtain ⟨c,C,hc,hC,hbound⟩ := SingularitiesUniform.uniform_nondegeneracy_symmetric
    hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ d
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound,SingularitiesSigns.actual_frontier_signs hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ] with z hz hs
  simpa only [hs] using hz

theorem uniform_nondegeneracy_nonbacktracking
    (hn : 0<n)
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
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) :
    let p := fun z j => Real.sign (Boundary.boundaryVector m z j).re
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
      c≤(quadraticCoefficient (p z) (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
          (stableCoefficient (p z) (d.r z) (d.K z)) ∧
      (quadraticCoefficient (p z) (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) (p z) (d.l z) (d.r z)
          (stableCoefficient (p z) (d.r z) (d.K z))≤C := by
  obtain ⟨c,C,hc,hC,hbound⟩ := SingularitiesUniform.uniform_nondegeneracy_nonbacktracking
    hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ d
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound,SingularitiesSigns.actual_frontier_signs hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ] with z hz hs
  simpa only [hs] using hz

end NonSymmetricDyson.Paper.SingularitiesMovingSigns
