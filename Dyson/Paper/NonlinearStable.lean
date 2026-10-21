import Dyson.Full.StrictBulkEndpoints
import Dyson.Full.MainLinearExceptional

/-! Theorem 7(i)–(ii) for the original zero-potential NB model.
The spectral separation parameters are quantified before the constants.
These proofs use the exact residual identity, quadratic absorption and the
large-height 4/η² estimate, including the full complex exclusion |z| ≥ δ. -/
noncomputable section
open Set
open scoped BigOperators
namespace NonSymmetricDyson.Paper.Nonlinear
open Full
universe u
variable {V : Type u} [Fintype V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

/-- Strict bulk, nonbipartite graph, all positive heights. -/
theorem main_theorem_seven_bulk (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)
    (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ StrictBulkModel.energySet m root ε → 0 < z.im → (∀ e, g e ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual G.matrix (fun _ => 0) z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual G.matrix (fun _ => 0) z g‖ := by
  exact StrictBulkModel.NB.nonlinear G root hd hc ext algebraic puiseux
    (fun _ => 0) (Or.inl hnb) ε hε

/-- Strict bulk outside a complex disc at zero. This covers Re z = 0 at
positive height and requires no nonbipartiteness assumption. -/
theorem main_theorem_seven_away (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ StrictBulkModel.energySet m root ε → δ ≤ ‖z‖ → 0 < z.im → (∀ e, g e ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual G.matrix (fun _ => 0) z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual G.matrix (fun _ => 0) z g‖ := by
  simpa only [Complex.ofReal_zero, sub_zero] using
    StrictBulkModel.NB.nonlinear_away G root hd hc ext algebraic puiseux 0 ε δ hε hδ

/-- Bipartite balance at a regular bulk origin. The reconstructed vertex
values are proved well-defined in the conclusion. The source's extra bounds
on residual and balance may be imposed without weakening this estimate. -/
theorem main_theorem_seven_balance [Nonempty V]
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hc : Resonance.StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (perron : BulkPerron.PerronLeftAndSimple.{u})
    (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper,
      BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
    (hregular : (0 : ℝ) ∉ Boundary.singularUnion m)
    (hbulk : BasicEstimates.IsUpperSolution (Boundary.boundaryVector m 0)) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      ‖z‖ ≤ r → 0 < z.im → ‖g - m z‖ ≤ c →
      (∀ y, z + Full.Nonlinear.NB.incidence G g y ≠ 0) ∧
      ‖g - m z‖ ≤ C * (‖Model.residual G.matrix (fun _ => 0) z g‖ +
        ‖∑ y, Exceptional.partitionSign part y *
          (Full.Nonlinear.NB.vertexValues G g z y -
            Full.Nonlinear.NB.vertexValues G (m z) z y)‖) := by
  exact Exceptional.NB.main_theorem_seven_balance G hd hc part hp algebraic puiseux
    perron m hupper heq hregular hbulk

end NonSymmetricDyson.Paper.Nonlinear
