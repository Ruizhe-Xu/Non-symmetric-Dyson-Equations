import Dyson.Paper.BulkTorus
import Dyson.Full.BulkMarkovComplete
import Dyson.Full.BulkMarkov
import Dyson.Full.BulkGraph
import Dyson.Full.BulkConnectivity
import Dyson.MatrixResonance

/-! Paper-facing graph and Markov lemmas for the bulk chapter. Circle-valued
vectors encode exactly unitary diagonal matrices; their ambient function
norm is the coordinate maximum norm used by the manuscript. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.BulkGraph
open Resonance Full
universe u
variable {V : Type u} [Fintype V]

def resonanceSet (Q : Matrix V V ℝ) : Set (V → Circle) :=
  {v | CycleResonant (fun i j => 0 < Q i j) v}

theorem zero_set_of_edge_defect (Q : Matrix V V ℝ) (root : V)
    (hconn : StronglyConnected (fun i j => 0 < Q i j)) (v : V → Circle) :
    PhaseDefect.delta (fun i j => 0 < Q i j) v = 0 ↔ v ∈ resonanceSet Q :=
  PhaseDefect.delta_eq_zero_iff_cycleResonant _ v root hconn

theorem minimizing_gauge (Q : Matrix V V ℝ) (v : V → Circle) :
    ∃ γ : V → Circle, PhaseDefect.delta (fun i j => 0 < Q i j) v =
      ‖fun e : PhaseDefect.Edge (fun i j => 0 < Q i j) =>
        (v e.val.1 : ℂ) - star (γ e.val.1 : ℂ) * (γ e.val.2 : ℂ)‖ := by
  obtain ⟨γ,hγ⟩ := PhaseDefect.exists_minimizer (fun i j => 0 < Q i j) v
  refine ⟨γ,?_⟩
  rw [PhaseDefect.delta_eq_minimum _ v γ hγ]
  unfold PhaseDefect.edgeDefect
  congr 1
  funext e
  simp only [PhaseDefect.edgeError,Circle.coe_mul,Circle.coe_inv_eq_conj,Complex.star_def]

/-- `lem:UminusQ-graph-resonance`, including the attained minimum positive
entry and the support-only order of quantifiers for its constant. -/
theorem phase_markov_resonance [Nonempty V]
    (basis : BulkTorus.IntegerRowBasis.{u}) (geometry : BulkTorus.CircleMetricFacts)
    (characters : BulkTorus.ContinuousCharacterClassification.{u})
    (E : V → V → Prop) (hc : StronglyConnected E) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : Matrix V V ℝ),
      (∀ i j, 0 ≤ Q i j) → (∀ i, ∑ j, Q i j = 1) →
      (∀ i j, E i j ↔ 0 < Q i j) →
      ∃ κ : ℝ, 0 < κ ∧ (∃ i j, Q i j = κ) ∧
        (∀ i j, 0 < Q i j → κ ≤ Q i j) ∧
        ∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 → ∀ (u : V → Circle) (w : V → ℂ),
          max (1-lam) (c * κ^(2*Fintype.card V) * (Full.BulkTorus.resonanceDistance E u)^2) * ‖w‖ ≤
            ‖MarkovStability.phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
  obtain ⟨c,hc',hh⟩ := Full.BulkMarkov.phase_markov_distance_bound
    (BulkTorus.finite_torus_error_bound basis geometry characters) E hc
  refine ⟨c,hc',?_⟩
  intro Q hQ hrow hs
  obtain ⟨κ,hκ,hκ1,hattain,hmin⟩ := Full.BulkMarkovComplete.positive_minimum Q hQ hrow
  refine ⟨κ,hκ,hattain,hmin,?_⟩
  intro lam hlam0 hlam1 u w
  exact hh Q hQ hrow κ hκ hκ1 (fun i j hij => hmin i j ((hs i j).mp hij)) u lam hlam0 hlam1 w

theorem symmetric_edge_constraint (E : V → V → Prop)
    (hsym : ∀ i j, E i j → E j i) (v : V → Circle)
    (hv : CycleResonant E v) {i j : V} (hij : E i j) : v i * v j = 1 :=
  Full.BulkGraph.symmetric_resonance_edge hsym v hv hij

theorem symmetric_bipartite_resonance (E : V → V → Prop)
    (hsym : ∀ i j, E i j → E j i) (root : V) (hc : StronglyConnected E)
    (part : Set V) (hp : Full.BulkGraph.IsBipartition (E := E) part) (v : V → Circle) :
    CycleResonant E v ↔ ∃ c : Circle, ∀ i, v i = if i ∈ part then c else c⁻¹ := by
  classical
  exact Full.BulkGraph.symmetric_bipartition_classification hsym root hc part hp v

theorem symmetric_nonbipartite_resonance (E : V → V → Prop)
    (hsym : ∀ i j, E i j → E j i) (root : V) (hc : StronglyConnected E)
    (hn : ¬∃ part : Set V, Full.BulkGraph.IsBipartition (E := E) part) (v : V → Circle) :
    CycleResonant E v ↔ v = 1 := by
  simpa only [funext_iff,Pi.one_apply] using
    Full.BulkGraph.symmetric_nonbipartite_classification hsym hc hn v

namespace NB
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

theorem strongly_connected (hd : ∀ y, 3 ≤ Full.BulkGraph.NB.degree G y)
    (hc : StronglyConnected G.Adj) : StronglyConnected G.CanFollow :=
  Full.BulkConnectivity.NB.stronglyConnected G
    (Full.BulkGraph.NB.hasThreeNeighbors_of_degree G hd) hc

/-- `lem.resonant-set-B`: the original numeric degree assumption and base
connectivity imply the full vertex-potential description. -/
theorem resonant_set (hd : ∀ y, 3 ≤ Full.BulkGraph.NB.degree G y)
    (hc : StronglyConnected G.Adj) (root : G.Edge) (v : G.Edge → Circle) :
    CycleResonant G.CanFollow v ↔
      ∃ ω : V → Circle, ∀ e, v e = (ω (G.tail e))⁻¹ * ω (G.head e) :=
  Full.BulkGraph.NB.resonance_iff_vertex_potentials G
    (Full.BulkGraph.NB.hasThreeNeighbors_of_degree G hd) root (strongly_connected G hd hc) v

end NB
end NonSymmetricDyson.Paper.BulkGraph
