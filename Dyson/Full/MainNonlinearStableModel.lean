import Dyson.Full.MainLinearExceptional
import Dyson.Full.NonlinearStable

/-! M7(i) on the actual canonical bulk boundary. -/
noncomputable section
open Set
namespace NonSymmetricDyson.Full.Nonlinear
universe u
variable {V : Type u} [Fintype V]

/-- Uniform stable-bulk nonlinear estimate for symmetric support.  Boundary
continuity and stability are consequences of the actual regular bulk model. -/
theorem main_theorem_seven_symmetric_bulk [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hconn : Resonance.StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ)))
    (hexception : ∀ E ∈ J, ¬ ((∀ i, a i = E) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : V → ℂ),
      z.re ∈ J → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual S a z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual S a z g‖ := by
  obtain ⟨hcont, hu, he⟩ := Exceptional.canonical_closed_strip_data algebraic puiseux S a hS m
    hupper heq J hregular hbulk
  have hbij : ∀ E ∈ J, Function.Bijective
      (InteriorStability.stabilityOperator S (Boundary.boundaryVector m (E : ℂ))) := by
    intro E hE
    exact BulkBoundary.symmetric_boundary_bijective S a E _ hS hconn hsymm (hbulk E hE)
      (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq E (hregular E hE)).2.2
      (hexception E hE)
  obtain ⟨c,C,hc,hC,hb⟩ := stable_strip_nonlinear_of_boundary_bijective S a J hJ
    (Boundary.boundaryVector m) hS hcont hu he hbij
  refine ⟨c,C,hc,hC,?_⟩
  intro z g hzJ hz hg0 hclose hres
  have hh := hb z g hzJ hz hg0
  rw [Boundary.family_extension_agrees S a hS m hupper heq z hz] at hh
  exact hh hclose hres

namespace NB

/-- M7(i) for an actual non-backtracking model: its canonical extension,
boundary invertibility, and uniform constants are all constructed. -/
theorem main_theorem_seven_bulk
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (a : V → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ)))
    (hexception : ∀ E ∈ J, ¬ ((∀ y, a y = E) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ J → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual G.matrix (G.terminalShift a) z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual G.matrix (G.terminalShift a) z g‖ := by
  obtain ⟨hcont, hu, he⟩ := Exceptional.canonical_closed_strip_data algebraic puiseux G.matrix
    (G.terminalShift a) G.matrix_nonnegative m hupper heq J hregular hbulk
  obtain ⟨c,C,hc,hC,hb⟩ := stable_bulk_nonlinear G a J hJ (Boundary.boundaryVector m)
    hd root hbase hcont hu he hexception
  refine ⟨c,C,hc,hC,?_⟩
  intro z g hzJ hz hg0 hclose hres
  have hh := hb z g hzJ hz hg0
  rw [Boundary.family_extension_agrees G.matrix (G.terminalShift a) G.matrix_nonnegative
    m hupper heq z hz] at hh
  exact hh hclose hres

end NB
end NonSymmetricDyson.Full.Nonlinear
