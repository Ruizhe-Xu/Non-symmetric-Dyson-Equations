import Dyson.Full.MainNonlinearExteriorModel
import Dyson.Full.BulkMatrixBridge

/-! The original NB off-support clause with no matrix irreducibility or
measure-support premise left to the caller. Those facts are derived from the
actual graph and the canonical solution. -/
noncomputable section
open Set
namespace NonSymmetricDyson.Paper.Nonlinear
open Full Full.BulkMatrixBridge
variable {V : Type*} [Fintype V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

/-- Canonical solutions commute with the exact finite change of coordinates. -/
theorem canonical_zero_reindex :
    GlobalWellPosedness.solution (matrix (Fintype.equivFin G.Edge) G.matrix)
      (vector (Fintype.equivFin G.Edge) (fun _ => 0))
      (fun _ _ => G.matrix_nonnegative _ _) =
    family (Fintype.equivFin G.Edge)
      (GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative) := by
  funext z
  by_cases hz : 0 < z.im
  · apply GlobalWellPosedness.solution_eq_of_upper_solution _ _ hz
    · exact (upper_reindex_iff _ _).mpr
        (GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    · exact (dyson_reindex_iff _ _ _ _ _).mpr
        (GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz)
  · ext j
    simp [GlobalWellPosedness.solution, hz, family, vector]

/-- Theorem 7(i), outside the geometric support, on every fixed bounded
horizontal spectral region and at all positive heights. -/
theorem main_theorem_seven_off_support (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory (Fin (Fintype.card G.Edge)))
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin (Fintype.card G.Edge)))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      |z.re| ≤ T → z.re ∈ StrictBulk.separated
        (closure (Boundary.regularSupport m root) ∪ Boundary.singularUnion m) ε →
      0 < z.im → (∀ j, g j ≠ 0) →
      ‖g-m z‖ ≤ c → ‖Model.residual G.matrix (fun _ => 0) z g‖ ≤ c →
      ‖g-m z‖ ≤ C * ‖Model.residual G.matrix (fun _ => 0) z g‖ := by
  let m := GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative
  let e := Fintype.equivFin G.Edge
  obtain ⟨hn,hS,hirr,_,_⟩ := BulkMatrixBridge.NB.fin_model_data G hd hc root (fun _ => 0) m
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz)
  obtain ⟨c,C,hc',hC,hb⟩ := Full.Nonlinear.main_theorem_seven_exterior_model hn ext algebraic
    puiseux inversion (matrix e G.matrix) (vector e (fun _ => 0)) hS hirr (e root) T ε hT hε
  rw [canonical_zero_reindex G] at hb
  refine ⟨c,C,hc',hC,?_⟩
  intro z g hTz hsep hz hg hclose hres
  have hs : z.re ∈ StrictBulk.separated
      (closure (Boundary.regularSupport (family e m) (e root)) ∪
        Boundary.singularUnion (family e m)) ε := by
    simpa only [regularSupport_reindex, singularUnion_reindex] using hsep
  have hh := hb z (vector e g) hTz hs hz (fun j => hg (e.symm j))
    (by simpa only [family,e,m,norm_vector_sub] using hclose)
    (by simpa only [norm_residual_reindex] using hres)
  simpa only [family,e,m,norm_vector_sub,norm_residual_reindex] using hh

end NonSymmetricDyson.Paper.Nonlinear
