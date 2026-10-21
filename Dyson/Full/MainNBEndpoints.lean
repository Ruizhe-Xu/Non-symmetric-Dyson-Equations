import Dyson.Full.BulkMatrixBridge
import Dyson.Full.MainSingularityEndpoints
import Dyson.Full.MainNonlinearPrescribedAnchor

/-! M5 and M7 directly on the actual oriented-edge space of an NB model.
The conversion to Fin(card Edge) is an exact representation change whose
positive-power irreducibility is proved from the graph hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Full.NBEndpoints
open BulkMatrixBridge Singularities Nonlinear

section Model
variable {V : Type*} [Fintype V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]
variable (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (a : V → ℝ) (m : ℂ → G.Edge → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
variable (τ : ℝ) (i : G.Edge) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)
include hd hc perron normalForm orientation algebraic puiseux hupper heq hfront hτ

theorem main_theorem_five_edge
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : G.Edge → ℝ) (C : ℝ), c ≠ 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        (c * (x - τ) < 0 →
          |Boundary.realDensity m j x - D j * rootRadius c 2 (x - τ)| ≤
            C * (rootRadius c 2 (x - τ)) ^ 2 ∧ 0 < Boundary.realDensity m j x) ∧
        (0 < c * (x - τ) → Boundary.realDensity m j x = 0) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularEdge (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hedge
  obtain ⟨c,D,C,hc',hD,hC,hb⟩ := Singularities.main_theorem_five_regular_edge perron normalForm orientation
    hn algebraic puiseux (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr
    (family e m) hu he τ (e i) hf hr ht
  refine ⟨c,fun j => D (e j),C,hc',fun j => hD (e j),hC,?_⟩
  filter_upwards [hb] with x hx j
  simpa [Boundary.realDensity, boundary_reindex, vector] using hx (e j)

theorem main_theorem_five_cusp
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : G.Edge → ℝ) (C : ℝ), c < 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        |Boundary.realDensity m j x - D j * rootRadius c 3 (x - τ)| ≤
          C * (rootRadius c 3 (x - τ)) ^ 2 ∧
        (x ≠ τ → 0 < Boundary.realDensity m j x) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularCusp (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hcusp
  obtain ⟨c,D,C,hc',hD,hC,hb⟩ := Singularities.main_theorem_five_regular_cusp perron normalForm orientation
    hn algebraic puiseux (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr
    (family e m) hu he τ (e i) hf hr ht
  refine ⟨c,fun j => D (e j),C,hc',fun j => hD (e j),hC,?_⟩
  filter_upwards [hb] with x hx j
  simpa [Boundary.realDensity, boundary_reindex, vector] using hx (e j)

variable (ift : AnalyticImplicitFunctionPrinciple
  (Fin (Fintype.card G.Edge) → ℂ) (ℂ × (Fin (Fintype.card G.Edge) → ℂ)))
variable (rootArgument : AnalyticRootFactorizationPrinciple)
include ift rootArgument

theorem main_theorem_seven_edge
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → G.Edge → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (G.terminalShift a) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((1 : ℝ) / 2) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularEdge (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hedge
  obtain ⟨H,r,c₀,C,hH,hr',hc₀,hC,hb⟩ := Nonlinear.main_theorem_seven_regular_edge
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he τ (e i) hf hr ht
  refine ⟨H,r,c₀,C,hH,hr',hc₀,hC,?_⟩
  intro x η η₀ E g htop hx hη hηH hE hgcont hg0 hclose hres
  have hh := hb x η η₀ E (fun t => vector e (g t)) htop hx hη hηH hE
    (continuous_family_reindex e g hgcont) (fun t ht j => hg0 t ht (e.symm j))
    (fun t ht => by simpa only [family, norm_vector_sub] using hclose t ht)
    (fun t ht => by simpa only [norm_residual_reindex] using hres t ht)
  simpa only [family, norm_vector_sub] using hh

theorem main_theorem_seven_cusp
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → G.Edge → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (G.terminalShift a) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((2 : ℝ) / 3) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularCusp (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hcusp
  obtain ⟨H,r,c₀,C,hH,hr',hc₀,hC,hb⟩ := Nonlinear.main_theorem_seven_regular_cusp
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he τ (e i) hf hr ht
  refine ⟨H,r,c₀,C,hH,hr',hc₀,hC,?_⟩
  intro x η η₀ E g htop hx hη hηH hE hgcont hg0 hclose hres
  have hh := hb x η η₀ E (fun t => vector e (g t)) htop hx hη hηH hE
    (continuous_family_reindex e g hgcont) (fun t ht j => hg0 t ht (e.symm j))
    (fun t ht => by simpa only [family, norm_vector_sub] using hclose t ht)
    (fun t ht => by simpa only [norm_residual_reindex] using hres t ht)
  simpa only [family, norm_vector_sub] using hh

theorem main_theorem_seven_edge_prescribed_anchor
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ)
    (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ H ≤ η₀ ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η E : ℝ) (g : ℝ → G.Edge → ℂ),
        |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (G.terminalShift a) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((1 : ℝ) / 2) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularEdge (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hedge
  obtain ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,hb⟩ := Nonlinear.main_theorem_seven_edge_prescribed_anchor
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he τ (e i) hf hr ht η₀ hη₀
  refine ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,?_⟩
  intro x η E g hx hη hηH hE hgcont hg0 hclose hres
  have hh := hb x η E (fun t => vector e (g t)) hx hη hηH hE
    (continuous_family_reindex e g hgcont) (fun t ht j => hg0 t ht (e.symm j))
    (fun t ht => by simpa only [family, norm_vector_sub] using hclose t ht)
    (fun t ht => by simpa only [norm_residual_reindex] using hres t ht)
  simpa only [family, norm_vector_sub] using hh

theorem main_theorem_seven_cusp_prescribed_anchor
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ)
    (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ H ≤ η₀ ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η E : ℝ) (g : ℝ → G.Edge → ℂ),
        |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (G.terminalShift a) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((2 : ℝ) / 3) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i a m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularCusp (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hcusp
  obtain ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,hb⟩ := Nonlinear.main_theorem_seven_cusp_prescribed_anchor
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he τ (e i) hf hr ht η₀ hη₀
  refine ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,?_⟩
  intro x η E g hx hη hηH hE hgcont hg0 hclose hres
  have hh := hb x η E (fun t => vector e (g t)) hx hη hηH hE
    (continuous_family_reindex e g hgcont) (fun t ht j => hg0 t ht (e.symm j))
    (fun t ht => by simpa only [family, norm_vector_sub] using hclose t ht)
    (fun t ht => by simpa only [norm_residual_reindex] using hres t ht)
  simpa only [family, norm_vector_sub] using hh

end Model
end NonSymmetricDyson.Full.NBEndpoints
