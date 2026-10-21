import Dyson.Paper.SingularityPoissonProfiles

/-! M5 supplies the local measure profiles, and direct Poisson integration
supplies the actual component imaginary-part estimates. No density-profile
or imaginary-part estimate is a hypothesis of these model theorems. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.SingularityPoissonModel
open Full Full.Singularities Foundations Boundary BoundaryMeasure
open SingularityPoissonProfiles SingularityPoissonOrientation

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


theorem cusp_symmetric
    (inversion : ExternalStieltjesInversion)
    (hcusp : IsRegularCusp (regularSupport m i) τ)
    (j : Fin n) (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    (hrep : Represents (fun z => m z j) μ) :
    ∃ c C ε : ℝ,0<c ∧ 0<C ∧ 0<ε ∧ ∀ E η : ℝ,0<η → |E|+η<ε →
      c*(|E|+η)^((1:ℝ)/3) ≤ (m (Poisson.point (τ+E) η) j).im ∧
      (m (Poisson.point (τ+E) η) j).im ≤ C*(|E|+η)^((1:ℝ)/3) := by
  obtain ⟨c,D,C,hc,hD,_,hloc⟩ := Singularities.regular_cusp_symmetric perron normalForm orientation hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ hcusp
  obtain ⟨lo,up,r,v,hlo,hup,hr,hv,hnv,hbounds,hmeasure⟩ :=
    cusp_profile_from_asymptotic algebraic puiseux inversion S a hS m hupper heq
      μ hμ j hrep τ hτ c (D j) C hc.ne (hD j)
      (hloc.mono fun x hx => (hx j).1)
  exact cusp_imaginary_from_profile μ hμ (fun z => m z j) hrep τ lo up r v
    hlo hup hr hv hnv hbounds hmeasure

/-- A single physical orientation works for every component; only the
positive constants and neighborhood radii depend on the component. -/
theorem edge_symmetric
    (inversion : ExternalStieltjesInversion)
    (hedge : IsRegularEdge (regularSupport m i) τ)
    (μ : Fin n → Measure ℝ) (hμ : ∀ j,IsProbabilityMeasure (μ j))
    (hrep : ∀ j,Represents (fun z => m z j) (μ j)) :
    ∃ left : Bool,∀ j,∃ cs Cs cg Cg ε : ℝ,
      0<cs ∧ 0<Cs ∧ 0<cg ∧ 0<Cg ∧ 0<ε ∧
      ∀ κ η : ℝ,0≤κ → 0<η → κ+η<ε →
        (cs*Real.sqrt (κ+η) ≤ (m (Poisson.point (τ+direction left*κ) η) j).im ∧
          (m (Poisson.point (τ+direction left*κ) η) j).im ≤ Cs*Real.sqrt (κ+η)) ∧
        (cg*(η/Real.sqrt (κ+η)) ≤ (m (Poisson.point (τ-direction left*κ) η) j).im ∧
          (m (Poisson.point (τ-direction left*κ) η) j).im ≤ Cg*(η/Real.sqrt (κ+η))) := by
  obtain ⟨c,D,C,hc,hD,_,hloc⟩ := Singularities.regular_edge_symmetric perron normalForm orientation hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ hedge
  have hdir : ∃ left:Bool,c*direction left<0 := by
    rcases lt_or_gt_of_ne hc with hn|hp
    · exact ⟨true,by simpa [direction] using hn⟩
    · exact ⟨false,by dsimp [direction];nlinarith⟩
  obtain ⟨left,hdir⟩ := hdir
  refine ⟨left,?_⟩
  intro j
  have hzero : realDensity m j τ=0 := by
    simp only [realDensity,regular_frontier_real hn algebraic puiseux S a hS hirr m
      hupper heq τ i hfront hτ j,zero_div]
  obtain ⟨lo,up,r,v,hlo,hup,hr,hv,hnv,hbounds,hmeasure⟩ :=
    edge_profile_from_asymptotic algebraic puiseux inversion S a hS m hupper heq
      (μ j) (hμ j) j (hrep j) τ hτ hzero c (D j) C hc (hD j) left hdir
      (hloc.mono fun x hx => ⟨fun hs => ((hx j).1 hs).1,(hx j).2⟩)
  exact edge_imaginary_from_profile (μ j) (hμ j) (fun z => m z j) (hrep j)
    τ left lo up r v hlo hup hr hv hnv hbounds hmeasure

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


theorem cusp_nonbacktracking
    (inversion : ExternalStieltjesInversion)
    (hcusp : IsRegularCusp (regularSupport m i) τ)
    (j : Fin n) (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ)
    (hrep : Represents (fun z => m z j) μ) :
    ∃ c C ε : ℝ,0<c ∧ 0<C ∧ 0<ε ∧ ∀ E η : ℝ,0<η → |E|+η<ε →
      c*(|E|+η)^((1:ℝ)/3) ≤ (m (Poisson.point (τ+E) η) j).im ∧
      (m (Poisson.point (τ+E) η) j).im ≤ C*(|E|+η)^((1:ℝ)/3) := by
  obtain ⟨c,D,C,hc,hD,_,hloc⟩ := Singularities.regular_cusp_nonbacktracking perron normalForm orientation hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ hcusp
  obtain ⟨lo,up,r,v,hlo,hup,hr,hv,hnv,hbounds,hmeasure⟩ :=
    cusp_profile_from_asymptotic algebraic puiseux inversion S a hS m hupper heq
      μ hμ j hrep τ hτ c (D j) C hc.ne (hD j)
      (hloc.mono fun x hx => (hx j).1)
  exact cusp_imaginary_from_profile μ hμ (fun z => m z j) hrep τ lo up r v
    hlo hup hr hv hnv hbounds hmeasure

/-- A single physical orientation works for every component; only the
positive constants and neighborhood radii depend on the component. -/
theorem edge_nonbacktracking
    (inversion : ExternalStieltjesInversion)
    (hedge : IsRegularEdge (regularSupport m i) τ)
    (μ : Fin n → Measure ℝ) (hμ : ∀ j,IsProbabilityMeasure (μ j))
    (hrep : ∀ j,Represents (fun z => m z j) (μ j)) :
    ∃ left : Bool,∀ j,∃ cs Cs cg Cg ε : ℝ,
      0<cs ∧ 0<Cs ∧ 0<cg ∧ 0<Cg ∧ 0<ε ∧
      ∀ κ η : ℝ,0≤κ → 0<η → κ+η<ε →
        (cs*Real.sqrt (κ+η) ≤ (m (Poisson.point (τ+direction left*κ) η) j).im ∧
          (m (Poisson.point (τ+direction left*κ) η) j).im ≤ Cs*Real.sqrt (κ+η)) ∧
        (cg*(η/Real.sqrt (κ+η)) ≤ (m (Poisson.point (τ-direction left*κ) η) j).im ∧
          (m (Poisson.point (τ-direction left*κ) η) j).im ≤ Cg*(η/Real.sqrt (κ+η))) := by
  obtain ⟨c,D,C,hc,hD,_,hloc⟩ := Singularities.regular_edge_nonbacktracking perron normalForm orientation hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ hedge
  have hdir : ∃ left:Bool,c*direction left<0 := by
    rcases lt_or_gt_of_ne hc with hn|hp
    · exact ⟨true,by simpa [direction] using hn⟩
    · exact ⟨false,by dsimp [direction];nlinarith⟩
  obtain ⟨left,hdir⟩ := hdir
  refine ⟨left,?_⟩
  intro j
  have hzero : realDensity m j τ=0 := by
    simp only [realDensity,regular_frontier_real hn algebraic puiseux S a hS hirr m
      hupper heq τ i hfront hτ j,zero_div]
  obtain ⟨lo,up,r,v,hlo,hup,hr,hv,hnv,hbounds,hmeasure⟩ :=
    edge_profile_from_asymptotic algebraic puiseux inversion S a hS m hupper heq
      (μ j) (hμ j) j (hrep j) τ hτ hzero c (D j) C hc (hD j) left hdir
      (hloc.mono fun x hx => ⟨fun hs => ((hx j).1 hs).1,(hx j).2⟩)
  exact edge_imaginary_from_profile (μ j) (hμ j) (fun z => m z j) (hrep j)
    τ left lo up r v hlo hup hr hv hnv hbounds hmeasure

end Nonbacktracking

end NonSymmetricDyson.Paper.SingularityPoissonModel
