import Dyson.Paper.Singularities
import Dyson.Paper.SingularitiesAsymptoticNormalization

/-! The revised main theorem in exactly its displayed square/cubic powers. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.SingularitiesAsymptotics
open Full Full.Singularities

section Symmetric

variable {n : ℕ}
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (hn : 0 < n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable (hsym : ∀ i j,S i j=S j i)
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)

include hsym perron normalForm orientation hn algebraic puiseux hS hirr hupper heq hfront hτ

/-- Literal square-root law and spectral gap with the original ± convention. -/
theorem edge_symmetric
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ (s : ℝ) (d : Fin n → ℝ) (B : ℝ), (s=1 ∨ s= -1) ∧ (∀ j,0<d j) ∧ 0<B ∧
      ∀ᶠ ω in 𝓝[Set.Ioi 0] 0, ∀ j,
        |Boundary.realDensity m j (τ+s*ω)-d j*Real.sqrt ω| ≤ B*ω ∧
        Boundary.realDensity m j (τ-s*ω)=0 := by
  obtain ⟨c,D,C,hc,hD,hC,hloc⟩ := Singularities.regular_edge_symmetric perron normalForm orientation hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ hedge
  apply SingularitiesAsymptoticNormalization.edge_power_form
    (fun j x => Boundary.realDensity m j x) τ c C D hc hD hC
  filter_upwards [hloc] with x hx j
  exact ⟨fun hs => ((hx j).1 hs).1,(hx j).2⟩

/-- Literal cubic-root law, with error O(|ω|^(2/3)) on both sides. -/
theorem cusp_symmetric
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ (d : Fin n → ℝ) (B : ℝ), (∀ j,0<d j) ∧ 0<B ∧
      ∀ᶠ ω:ℝ in 𝓝 0, ∀ j,
        |Boundary.realDensity m j (τ+ω)-d j*|ω|^((1:ℝ)/3)| ≤ B*|ω|^((2:ℝ)/3) := by
  obtain ⟨c,D,C,hc,hD,hC,hloc⟩ := Singularities.regular_cusp_symmetric perron normalForm orientation hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ hcusp
  apply SingularitiesAsymptoticNormalization.cusp_power_form
    (fun j x => Boundary.realDensity m j x) τ c C D hc.ne hD hC
  filter_upwards [hloc] with x hx j
  exact (hx j).1

end Symmetric

section Nonbacktracking

variable {n : ℕ}
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (hn : 0 < n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
variable (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
variable (av : V → ℝ) (hmat : ∀ i j,S i j=G.matrix (e i) (e j))
variable (hpot : ∀ i,a i=av (G.head (e i)))
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)

include deg hmat hpot perron normalForm orientation hn algebraic puiseux hS hirr hupper heq hfront hτ

/-- Literal square-root law and spectral gap with the original ± convention. -/
theorem edge_nonbacktracking
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ (s : ℝ) (d : Fin n → ℝ) (B : ℝ), (s=1 ∨ s= -1) ∧ (∀ j,0<d j) ∧ 0<B ∧
      ∀ᶠ ω in 𝓝[Set.Ioi 0] 0, ∀ j,
        |Boundary.realDensity m j (τ+s*ω)-d j*Real.sqrt ω| ≤ B*ω ∧
        Boundary.realDensity m j (τ-s*ω)=0 := by
  obtain ⟨c,D,C,hc,hD,hC,hloc⟩ := Singularities.regular_edge_nonbacktracking perron normalForm orientation hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ hedge
  apply SingularitiesAsymptoticNormalization.edge_power_form
    (fun j x => Boundary.realDensity m j x) τ c C D hc hD hC
  filter_upwards [hloc] with x hx j
  exact ⟨fun hs => ((hx j).1 hs).1,(hx j).2⟩

/-- Literal cubic-root law, with error O(|ω|^(2/3)) on both sides. -/
theorem cusp_nonbacktracking
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ (d : Fin n → ℝ) (B : ℝ), (∀ j,0<d j) ∧ 0<B ∧
      ∀ᶠ ω:ℝ in 𝓝 0, ∀ j,
        |Boundary.realDensity m j (τ+ω)-d j*|ω|^((1:ℝ)/3)| ≤ B*|ω|^((2:ℝ)/3) := by
  obtain ⟨c,D,C,hc,hD,hC,hloc⟩ := Singularities.regular_cusp_nonbacktracking perron normalForm orientation hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ hcusp
  apply SingularitiesAsymptoticNormalization.cusp_power_form
    (fun j x => Boundary.realDensity m j x) τ c C D hc.ne hD hC
  filter_upwards [hloc] with x hx j
  exact (hx j).1

end Nonbacktracking

end NonSymmetricDyson.Paper.SingularitiesAsymptotics
