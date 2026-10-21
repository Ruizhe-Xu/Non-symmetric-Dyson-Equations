import Dyson.Full.EuclideanReindex
import Dyson.Full.MainLinearEndpoints

/-! Literal M6 edge/cusp bounds for the nonbacktracking graph model.
The graph hypotheses imply the required matrix irreducibility internally,
and coordinate permutation preserves the actual Euclidean inverse norm. -/
noncomputable section
open scoped Topology
namespace NonSymmetricDyson.Full.BulkMatrixBridge.NB
open Singularities ExternalAlgebraic
variable {X : Type*} [Fintype X] (G : Nonbacktracking.BaseGraph X) [Fintype G.Edge]

theorem main_theorem_six_nb_edge
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
    (puiseux : ConvergentPuiseuxTheory)
    (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : Resonance.StronglyConnected G.Adj)
    (a : X → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (τ : ℝ) (root : G.Edge)
    (hfront : τ ∈ frontier (Boundary.regularSupport m root))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularEdge (Boundary.regularSupport m root) τ) :
    ∃ δ c C : ℝ,0<δ ∧ 0<c ∧ 0<C ∧
      ∀ (z : ℂ) (hz : 0<z.im),|z.re-τ|≤δ →
        c*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2))≤
          ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
            G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
            G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖≤
          C*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := fin_model_data G hd hc root a m hupper heq
  have hfront' : τ ∈ frontier (Boundary.regularSupport (family e m) (e root)) := by
    simpa only [regularSupport_reindex] using hfront
  have hτ' : τ ∉ Boundary.singularUnion (family e m) := by
    simpa only [singularUnion_reindex] using hτ
  have hkind' : IsRegularEdge (Boundary.regularSupport (family e m) (e root)) τ := by
    simpa only [regularSupport_reindex] using hkind
  obtain ⟨δ,c,C,hδ,hcpos,hC,hbound⟩ := MainLinearSingular.main_theorem_six_edge
    perron normalForm orientation hn algebraic puiseux
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he
    τ (e root) hfront' hτ' hkind'
  refine ⟨δ,c,C,hδ,hcpos,hC,?_⟩
  intro z hz hdist
  have hh := hbound z hz hdist
  have hnorm := stability_inverse_norm_reindex e G.matrix (G.terminalShift a) z (m z)
    G.matrix_nonnegative hz (hupper z hz) (heq z hz)
  simpa only [family,hnorm] using hh

theorem main_theorem_six_nb_cusp
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
    (puiseux : ConvergentPuiseuxTheory)
    (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : Resonance.StronglyConnected G.Adj)
    (a : X → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (τ : ℝ) (root : G.Edge)
    (hfront : τ ∈ frontier (Boundary.regularSupport m root))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularCusp (Boundary.regularSupport m root) τ) :
    ∃ δ c C : ℝ,0<δ ∧ 0<c ∧ 0<C ∧
      ∀ (z : ℂ) (hz : 0<z.im),|z.re-τ|≤δ →
        c*max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3))≤
          ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
            G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
            G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖≤
          C*max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := fin_model_data G hd hc root a m hupper heq
  have hfront' : τ ∈ frontier (Boundary.regularSupport (family e m) (e root)) := by
    simpa only [regularSupport_reindex] using hfront
  have hτ' : τ ∉ Boundary.singularUnion (family e m) := by
    simpa only [singularUnion_reindex] using hτ
  have hkind' : IsRegularCusp (Boundary.regularSupport (family e m) (e root)) τ := by
    simpa only [regularSupport_reindex] using hkind
  obtain ⟨δ,c,C,hδ,hcpos,hC,hbound⟩ := MainLinearSingular.main_theorem_six_cusp
    perron normalForm orientation hn algebraic puiseux
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr (family e m) hu he
    τ (e root) hfront' hτ' hkind'
  refine ⟨δ,c,C,hδ,hcpos,hC,?_⟩
  intro z hz hdist
  have hh := hbound z hz hdist
  have hnorm := stability_inverse_norm_reindex e G.matrix (G.terminalShift a) z (m z)
    G.matrix_nonnegative hz (hupper z hz) (heq z hz)
  simpa only [family,hnorm] using hh

end NonSymmetricDyson.Full.BulkMatrixBridge.NB
