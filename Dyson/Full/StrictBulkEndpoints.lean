import Dyson.Full.StrictBulkModel
import Dyson.Full.MainLinearBulkModel
import Dyson.Full.MainNonlinearStableModel
import Dyson.Full.MainConstantPotential
import Dyson.Full.MainNonlinearAway

/-! M6/M7 on the manuscript's actual separated strict-bulk set.
The canonical solution, its representing measures, all boundary data, and
compactness are constructed before invoking the uniform stability results. -/
noncomputable section
open Set
open scoped Topology
namespace NonSymmetricDyson.Full.StrictBulkModel
open Resonance
universe u
variable {V : Type u} [Fintype V]

def inverseNorm (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (z : ℂ) (hz : 0 < z.im) : ℝ :=
  ‖EuclideanInverse.stabilityInverse S a z (GlobalWellPosedness.solution S a hS z) hS hz
    (GlobalWellPosedness.solution_upper a hS hz)
    (GlobalWellPosedness.solution_equation a hS hz)‖

theorem positive_support_connected (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0)) :
    StronglyConnected (fun i j => 0 < S i j) := by
  have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
    funext i j
    exact propext (lt_iff_le_and_ne.trans (by simp [hS i j,ne_comm]))
  rwa [he]

/-- The literal ordinary symmetric strict-bulk clause of M6. -/
theorem symmetric_linear [Nonempty V]
    (ext : Foundations.ExternalStieltjesTheory V)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hstable : (¬ ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part) ∨
      ¬ ∃ t : ℝ, ∀ i, a i = t)
    (i : V) (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution S a hS
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ,
      z.re ∈ energySet m i ε → ∀ hz : 0 < z.im,
        c ≤ inverseNorm S a hS z hz ∧ inverseNorm S a hS z hz ≤ C := by
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux S a hS hc i ε hε
  apply MainLinearModel.main_theorem_six_symmetric_bulk algebraic puiseux S a hS hc hsymm _
    (fun z hz => GlobalWellPosedness.solution_upper a hS hz)
    (fun z hz => GlobalWellPosedness.solution_equation a hS hz) _ hJ hreg hbulk
  intro E _ h
  rcases hstable with hn | ha
  · exact hn h.2
  · exact ha ⟨E,h.1⟩

/-- The literal constant-potential symmetric strict-bulk clause of M6. -/
theorem symmetric_exceptional [Nonempty V]
    (ext : Foundations.ExternalStieltjesTheory V)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (perron : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (a : ℝ) (i : V) (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution S (fun _ => a) hS
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ,
      z.re ∈ energySet m i ε → ∀ hz : 0 < z.im,
        c * max 1 ‖z-(a:ℂ)‖⁻¹ ≤ inverseNorm S (fun _ => a) hS z hz ∧
        inverseNorm S (fun _ => a) hS z hz ≤ C * max 1 ‖z-(a:ℂ)‖⁻¹ := by
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux S (fun _ => a) hS hc i ε hε
  exact Exceptional.main_theorem_six_symmetric_exceptional algebraic puiseux perron S hS
    (positive_support_connected S hS hc) hsymm part hp a _
    (fun z hz => GlobalWellPosedness.solution_upper _ hS hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ hS hz) _ hJ hreg hbulk

namespace NB
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

theorem support_connected (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hbase : StronglyConnected G.Adj) :
    StronglyConnected (fun e f => G.matrix e f ≠ 0) := by
  have he : (fun e f => G.matrix e f ≠ 0) = G.CanFollow := by
    funext e f
    exact propext (by by_cases h : G.CanFollow e f <;> simp [Nonbacktracking.BaseGraph.matrix,h])
  rw [he]
  exact BulkConnectivity.NB.stronglyConnected G hd hbase

/-- The literal ordinary non-backtracking strict-bulk clause of M6. -/
theorem linear (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (a : V → ℝ)
    (hstable : (¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part) ∨
      ¬ ∃ t : ℝ, ∀ i, a i = t)
    (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ,
      z.re ∈ energySet m root ε → ∀ hz : 0 < z.im,
        c ≤ inverseNorm G.matrix (G.terminalShift a) G.matrix_nonnegative z hz ∧
        inverseNorm G.matrix (G.terminalShift a) G.matrix_nonnegative z hz ≤ C := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux G.matrix
    (G.terminalShift a) G.matrix_nonnegative (support_connected G hd hbase) root ε hε
  apply MainLinearModel.NB.main_theorem_six_bulk G root hd hbase algebraic puiseux a _
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) _ hJ hreg hbulk
  intro E _ h
  rcases hstable with hn | ha
  · exact hn h.2
  · exact ha ⟨E,h.1⟩

/-- The literal constant-potential non-backtracking strict-bulk clause of M6. -/
theorem exceptional (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (perron : BulkPerron.PerronLeftAndSimple.{u})
    (a : ℝ) (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => a) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ,
      z.re ∈ energySet m root ε → ∀ hz : 0 < z.im,
        c * max 1 ‖z-(a:ℂ)‖⁻¹ ≤ inverseNorm G.matrix (fun _ => a) G.matrix_nonnegative z hz ∧
        inverseNorm G.matrix (fun _ => a) G.matrix_nonnegative z hz ≤ C * max 1 ‖z-(a:ℂ)‖⁻¹ := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux G.matrix
    (fun _ => a) G.matrix_nonnegative (support_connected G hd hbase) root ε hε
  exact Exceptional.NB.main_theorem_six_exceptional G root hd hbase part hp algebraic puiseux perron a _
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) _ hJ hreg hbulk

/-- M7(i) on the literal strict-bulk set for a stable NB model. -/
theorem nonlinear (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (a : V → ℝ)
    (hstable : (¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part) ∨
      ¬ ∃ t : ℝ, ∀ i, a i = t)
    (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ energySet m root ε → 0 < z.im → (∀ e, g e ≠ 0) →
      ‖g-m z‖ ≤ c → ‖Model.residual G.matrix (G.terminalShift a) z g‖ ≤ c →
      ‖g-m z‖ ≤ C * ‖Model.residual G.matrix (G.terminalShift a) z g‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux G.matrix
    (G.terminalShift a) G.matrix_nonnegative (support_connected G hd hbase) root ε hε
  apply Nonlinear.NB.main_theorem_seven_bulk G root hd hbase algebraic puiseux a _
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) _ hJ hreg hbulk
  intro E _ h
  rcases hstable with hn | ha
  · exact hn h.2
  · exact ha ⟨E,h.1⟩

/-- The source's stable bipartite regime excludes a complex disc, so it
also includes positive heights above the exceptional real energy. -/
theorem nonlinear_away (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : StronglyConnected G.Adj)
    (ext : Foundations.ExternalStieltjesTheory G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (a ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => a) G.matrix_nonnegative
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ energySet m root ε → δ ≤ ‖z-(a:ℂ)‖ → 0 < z.im → (∀ e, g e ≠ 0) →
      ‖g-m z‖ ≤ c → ‖Model.residual G.matrix (fun _ => a) z g‖ ≤ c →
      ‖g-m z‖ ≤ C * ‖Model.residual G.matrix (fun _ => a) z g‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨hJ,hreg,hbulk⟩ := canonical_energySet_data ext algebraic puiseux G.matrix
    (fun _ => a) G.matrix_nonnegative (support_connected G hd hbase) root ε hε
  exact Nonlinear.NB.main_theorem_seven_away G root hd hbase algebraic puiseux a _
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) _ hJ hreg hbulk δ hδ

end NB
end NonSymmetricDyson.Full.StrictBulkModel
