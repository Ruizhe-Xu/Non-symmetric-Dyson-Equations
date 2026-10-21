import Dyson.Paper.NonlinearFrontier
import Dyson.Full.BulkMatrixBridge

/-! Theorem 7(iii), on the original oriented-edge space, with zero potential.
The fixed anchor is quantified before c₀, as required by the explicit
counterexample in Paper.AnchorObstruction. All constants precede g and E. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.Nonlinear
open Full Full.BulkMatrixBridge Full.Singularities Full.Nonlinear

section Model
variable {V : Type*} [Fintype V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]
variable (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (m : ℂ → G.Edge → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
variable (τ : ℝ) (i : G.Edge) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)
include hd hc perron normalForm orientation algebraic puiseux hupper heq hfront hτ

variable (ift : AnalyticImplicitFunctionPrinciple
  (Fin (Fintype.card G.Edge) → ℂ) (ℂ × (Fin (Fintype.card G.Edge) → ℂ)))
variable (rootArgument : AnalyticRootFactorizationPrinciple)
include ift rootArgument

theorem main_theorem_seven_edge_prescribed_anchor
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ)
    (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ H ≤ η₀ ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η E : ℝ) (g : ℝ → G.Edge → ℂ),
        |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (fun _ => 0) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((1 : ℝ) / 2) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i (fun _ => 0) m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularEdge (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hedge
  obtain ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,hb⟩ := fin_nb_edge_prescribed_anchor
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (fun _ => 0)) hS hirr
    G hd e.symm (fun _ _ => rfl) (fun _ => rfl) (family e m) hu he τ (e i) hf hr ht η₀ hη₀
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
        (∀ t ∈ Icc η η₀, ‖Model.residual G.matrix (fun _ => 0) (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((2 : ℝ) / 3) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc i (fun _ => 0) m hupper heq
  have hf : τ ∈ frontier (Boundary.regularSupport (family e m) (e i)) := by
    simpa only [regularSupport_reindex] using hfront
  have hr : τ ∉ Boundary.singularUnion (family e m) := by simpa only [singularUnion_reindex] using hτ
  have ht : IsRegularCusp (Boundary.regularSupport (family e m) (e i)) τ := by
    simpa only [regularSupport_reindex] using hcusp
  obtain ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,hb⟩ := fin_nb_cusp_prescribed_anchor
    perron normalForm orientation algebraic puiseux ift rootArgument hn
    (matrix e G.matrix) (vector e (fun _ => 0)) hS hirr
    G hd e.symm (fun _ _ => rfl) (fun _ => rfl) (family e m) hu he τ (e i) hf hr ht η₀ hη₀
  refine ⟨H,r,c₀,C,hH,hHcap,hr',hc₀,hC,?_⟩
  intro x η E g hx hη hηH hE hgcont hg0 hclose hres
  have hh := hb x η E (fun t => vector e (g t)) hx hη hηH hE
    (continuous_family_reindex e g hgcont) (fun t ht j => hg0 t ht (e.symm j))
    (fun t ht => by simpa only [family, norm_vector_sub] using hclose t ht)
    (fun t ht => by simpa only [norm_residual_reindex] using hres t ht)
  simpa only [family, norm_vector_sub] using hh

end Model
end NonSymmetricDyson.Paper.Nonlinear
