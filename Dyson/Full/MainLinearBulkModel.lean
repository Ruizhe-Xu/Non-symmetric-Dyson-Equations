import Dyson.Full.MainLinearExceptional

/-! M6 ordinary-bulk estimates from the canonical boundary of the actual
upper-half-plane Dyson solution. -/
noncomputable section
open Set
namespace NonSymmetricDyson.Full.MainLinearModel
universe u
variable {V : Type u} [Fintype V]

/-- The canonical extension and its boundary stability are constructed from
regular strict-bulk hypotheses. -/
theorem main_theorem_six_symmetric_bulk [Nonempty V]
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
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤ C := by
  obtain ⟨hcont, hu, he⟩ := Exceptional.canonical_closed_strip_data algebraic puiseux S a hS m
    hupper heq J hregular hbulk
  obtain ⟨c,C,hc,hC,hb⟩ := MainLinearBulk.main_theorem_six_symmetric_bulk J hJ S a
    (Boundary.boundaryVector m) hS hcont hu he hconn hsymm hexception
  refine ⟨c,C,hc,hC,?_⟩
  intro z hzJ hz
  simpa only [Boundary.family_extension_agrees S a hS m hupper heq z hz] using hb z hzJ hz

namespace NB

/-- The literal stable-bulk M6 conclusion for the original NB solution. -/
theorem main_theorem_six_bulk
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
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c ≤ ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ≤ C := by
  letI : Nonempty V := ⟨G.head root⟩
  obtain ⟨hcont, hu, he⟩ := Exceptional.canonical_closed_strip_data algebraic puiseux G.matrix
    (G.terminalShift a) G.matrix_nonnegative m hupper heq J hregular hbulk
  obtain ⟨c,C,hc,hC,hb⟩ := MainLinearBulk.NB.main_theorem_six_bulk G root J hJ a
    (Boundary.boundaryVector m) hd hbase hcont hu he hexception
  refine ⟨c,C,hc,hC,?_⟩
  intro z hzJ hz
  simpa only [Boundary.family_extension_agrees G.matrix (G.terminalShift a)
    G.matrix_nonnegative m hupper heq z hz] using hb z hzJ hz

end NB
end NonSymmetricDyson.Full.MainLinearModel
