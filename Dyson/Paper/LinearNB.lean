import Dyson.Paper.LinearCusp
import Dyson.Paper.LinearEdge
import Dyson.Full.EuclideanReindex

/-! The paper-facing NB bounds on the actual oriented-edge coordinate space.
Graph connectivity supplies irreducibility, and Euclidean reindexing is exact. -/
noncomputable section
open scoped Topology
namespace NonSymmetricDyson.Paper.LinearNB
open Full Full.Singularities Full.ExternalAlgebraic Full.Spectral Full.PerronContinuation
open Full.BulkMatrixBridge
variable {X : Type*} [Fintype X] (G : Nonbacktracking.BaseGraph X) [Fintype G.Edge]

theorem cusp
    (stieltjes : Foundations.ExternalStieltjesTheory (Fin (Fintype.card G.Edge)))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin (Fintype.card G.Edge)))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
    (puiseux : ConvergentPuiseuxTheory)
    (hd : Full.BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (a : X → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (τ : ℝ) (root : G.Edge)
    (hfront : τ ∈ frontier (Boundary.regularSupport m root))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularCusp (Boundary.regularSupport m root) τ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
          G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := NB.fin_model_data G hd hc root a m hupper heq
  have hfront' : τ ∈ frontier (Boundary.regularSupport (family e m) (e root)) := by
    simpa only [regularSupport_reindex] using hfront
  have hτ' : τ ∉ Boundary.singularUnion (family e m) := by
    simpa only [singularUnion_reindex] using hτ
  have hkind' : IsRegularCusp (Boundary.regularSupport (family e m) (e root)) τ := by
    simpa only [regularSupport_reindex] using hkind
  obtain ⟨δ,C,hδ,hC,hbound⟩ := LinearCusp.cusp_nonbacktracking hn stieltjes inversion perron
    continuousPerron spectral normalForm orientation algebraic puiseux
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr G hd e.symm a
    (fun _ _ => rfl) (fun _ => rfl) (family e m) hu he τ (e root) hfront' hτ' hkind'
  refine ⟨δ,C,hδ,hC,?_⟩
  intro z hz hdist
  have hh := hbound z hz hdist
  have hnorm := stability_inverse_norm_reindex e G.matrix (G.terminalShift a) z (m z)
    G.matrix_nonnegative hz (hupper z hz) (heq z hz)
  simpa only [family,hnorm] using hh

theorem edge
    (stieltjes : Foundations.ExternalStieltjesTheory (Fin (Fintype.card G.Edge)))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin (Fintype.card G.Edge)))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
    (puiseux : ConvergentPuiseuxTheory)
    (hd : Full.BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (a : X → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (τ : ℝ) (root : G.Edge)
    (hfront : τ ∈ frontier (Boundary.regularSupport m root))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularEdge (Boundary.regularSupport m root) τ) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) ≤
          ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
            G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
          G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) := by
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,hu,he⟩ := NB.fin_model_data G hd hc root a m hupper heq
  have hfront' : τ ∈ frontier (Boundary.regularSupport (family e m) (e root)) := by
    simpa only [regularSupport_reindex] using hfront
  have hτ' : τ ∉ Boundary.singularUnion (family e m) := by
    simpa only [singularUnion_reindex] using hτ
  have hkind' : IsRegularEdge (Boundary.regularSupport (family e m) (e root)) τ := by
    simpa only [regularSupport_reindex] using hkind
  obtain ⟨δ,c,C,hδ,hcpos,hC,hbound⟩ := LinearEdge.edge_nonbacktracking hn stieltjes inversion perron
    continuousPerron spectral normalForm orientation algebraic puiseux
    (matrix e G.matrix) (vector e (G.terminalShift a)) hS hirr G hd e.symm a
    (fun _ _ => rfl) (fun _ => rfl) (family e m) hu he τ (e root) hfront' hτ' hkind'
  refine ⟨δ,c,C,hδ,hcpos,hC,?_⟩
  intro z hz hdist
  have hh := hbound z hz hdist
  have hnorm := stability_inverse_norm_reindex e G.matrix (G.terminalShift a) z (m z)
    G.matrix_nonnegative hz (hupper z hz) (heq z hz)
  simpa only [family,hnorm] using hh

end NonSymmetricDyson.Paper.LinearNB
