import Dyson.Full.BulkGraph
import Mathlib

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkConnectivity
open Resonance Nonbacktracking

variable {V : Type*} [Fintype V]

/-- A finite doubly stochastic flow cannot increase a real function strictly
along any edge while increasing it weakly along every edge. -/
theorem doubly_stochastic_edge_eq (Q : Matrix V V ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (hcol : ∀ j, ∑ i, Q i j = 1) (f : V → ℝ)
    (hmono : ∀ i j, 0 < Q i j → f i ≤ f j)
    (i j : V) (hij : 0 < Q i j) : f i = f j := by
  have hn (i j : V) : 0 ≤ Q i j * (f j - f i) := by
    by_cases hp : 0 < Q i j
    · exact mul_nonneg (hQ i j) (sub_nonneg.mpr (hmono i j hp))
    · have hz : Q i j = 0 := le_antisymm (le_of_not_gt hp) (hQ i j)
      simp [hz]
  have hz : (∑ i, ∑ j, Q i j * (f j - f i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hleft : (∑ i, ∑ j, Q i j * f j) = ∑ j, f j := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol, one_mul]
    have hright : (∑ i, ∑ j, Q i j * f i) = ∑ i, f i := by
      simp_rw [← Finset.sum_mul, hrow, one_mul]
    rw [hleft, hright, sub_self]
  have hzi : (∑ j, Q i j * (f j - f i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))).mp hz i (Finset.mem_univ i)
  have hzij : Q i j * (f j - f i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)).mp hzi j (Finset.mem_univ j)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzij).resolve_left (ne_of_gt hij))).symm

theorem reverse_walk_of_doubly_stochastic (E : V → V → Prop)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1)
    (hsupport : ∀ i j, 0 < Q i j ↔ E i j)
    (a b : V) (hab : E a b) : Nonempty (Walk E b a) := by
  let f : V → ℝ := fun x => if Nonempty (Walk E b x) then 1 else 0
  have hm : ∀ i j, 0 < Q i j → f i ≤ f j := by
    intro i j hij
    by_cases hi : Nonempty (Walk E b i)
    · obtain ⟨p⟩ := hi
      have hj : Nonempty (Walk E b j) :=
        ⟨p.append (Walk.cons ((hsupport i j).mp hij) (Walk.nil j))⟩
      have hi' : Nonempty (Walk E b i) := ⟨p⟩
      simp [f, hi', hj]
    · by_cases hj : Nonempty (Walk E b j) <;> simp [f, hi, hj]
  have he := doubly_stochastic_edge_eq Q hQ hrow hcol f hm a b
    ((hsupport a b).mpr hab)
  have hb : Nonempty (Walk E b b) := ⟨Walk.nil b⟩
  by_contra ha
  simp [f, ha, hb] at he

namespace NB

variable (G : BaseGraph V)

def successors (e : G.Edge) : Finset G.Edge := Finset.univ.filter (G.CanFollow e)

/-- The successor count only depends on the head of the incoming edge.
The omitted reverse edge is one member of the same outgoing fibre. -/
theorem successors_card (e : G.Edge) :
    (successors G e).card =
      (Finset.univ.filter (fun f : G.Edge => G.tail f = G.head e)).card - 1 := by
  have hmem : G.reverse e ∈ Finset.univ.filter
      (fun f : G.Edge => G.tail f = G.head e) := by simp
  have heq : successors G e =
      (Finset.univ.filter (fun f : G.Edge => G.tail f = G.head e)).erase (G.reverse e) := by
    ext f
    simp only [successors, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, BaseGraph.CanFollow]
    have he : f = G.reverse e ↔ G.tail f = G.head e ∧ G.head f = G.tail e := by
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨h₁, h₂⟩
        apply Subtype.ext
        exact Prod.ext h₁ h₂
    simp only [ne_eq, he]
    have hh : G.head e = G.tail f ↔ G.tail f = G.head e := eq_comm
    rw [hh]
    tauto
  rw [heq, Finset.card_erase_of_mem hmem]

theorem successor_count_on_transition (e f : G.Edge) (hef : G.CanFollow e f) :
    (successors G e).card = (successors G (G.reverse f)).card := by
  rw [successors_card, successors_card, BaseGraph.reverse_head, hef.1]

def transition (e f : G.Edge) : ℝ :=
  if G.CanFollow e f then ((successors G e).card : ℝ)⁻¹ else 0

theorem successor_nonempty (hd : BulkGraph.NB.HasThreeNeighbors G) (e : G.Edge) :
    (successors G e).Nonempty := by
  obtain ⟨x, hx, hne, _⟩ := hd (G.head e) (G.tail e) (G.tail e)
  refine ⟨⟨(G.head e, x), hx⟩, ?_⟩
  simp only [successors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨rfl, hne⟩

theorem transition_nonnegative (e f : G.Edge) : 0 ≤ transition G e f := by
  unfold transition
  split <;> positivity

theorem transition_support (hd : BulkGraph.NB.HasThreeNeighbors G) (e f : G.Edge) :
    0 < transition G e f ↔ G.CanFollow e f := by
  have hc : (0 : ℝ) < (successors G e).card := by
    exact_mod_cast Finset.card_pos.mpr (successor_nonempty G hd e)
  unfold transition
  split <;> simp_all

theorem transition_row_sum (hd : BulkGraph.NB.HasThreeNeighbors G) (e : G.Edge) :
    ∑ f, transition G e f = 1 := by
  have hc : ((successors G e).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr (successor_nonempty G hd e)))
  simp only [transition, ← Finset.sum_filter]
  change (∑ _f ∈ successors G e, ((successors G e).card : ℝ)⁻¹) = 1
  simpa using mul_inv_cancel₀ hc

theorem transition_reversal (e f : G.Edge) :
    transition G e f = transition G (G.reverse f) (G.reverse e) := by
  by_cases h : G.CanFollow e f
  · simp [transition, h, (G.canFollow_reverse_iff e f).mp h,
      successor_count_on_transition G e f h]
  · simp [transition, h, ← G.canFollow_reverse_iff e f]

theorem transition_col_sum (hd : BulkGraph.NB.HasThreeNeighbors G) (f : G.Edge) :
    ∑ e, transition G e f = 1 := by
  simp_rw [transition_reversal G _ f]
  have hp : Function.Bijective G.reverse := Function.Involutive.bijective G.reverse_reverse
  rw [← Fintype.sum_bijective G.reverse hp (fun e => transition G (G.reverse f) e)
    (fun e => transition G (G.reverse f) (G.reverse e)) (fun _ => rfl)]
  exact transition_row_sum G hd (G.reverse f)

theorem reverse_walk (hd : BulkGraph.NB.HasThreeNeighbors G)
    (e f : G.Edge) (hef : G.CanFollow e f) : Nonempty (Walk G.CanFollow f e) :=
  reverse_walk_of_doubly_stochastic G.CanFollow (transition G)
    (transition_nonnegative G) (transition_row_sum G hd) (transition_col_sum G hd)
    (transition_support G hd) e f hef

theorem same_tail_walk (hd : BulkGraph.NB.HasThreeNeighbors G)
    (e f : G.Edge) (ht : G.tail e = G.tail f) : Nonempty (Walk G.CanFollow e f) := by
  obtain ⟨x, hx, hxe, hxf⟩ := hd (G.tail e) (G.head e) (G.head f)
  let incoming : G.Edge := ⟨(x, G.tail e), G.symm hx⟩
  have he : G.CanFollow incoming e := ⟨rfl, Ne.symm hxe⟩
  have hf : G.CanFollow incoming f := ⟨ht, Ne.symm hxf⟩
  obtain ⟨p⟩ := reverse_walk G hd incoming e he
  exact ⟨p.append (Walk.cons hf (Walk.nil f))⟩

theorem lift_base_walk (hd : BulkGraph.NB.HasThreeNeighbors G)
    {a b : V} (p : Walk G.Adj a b) :
    ∀ (e f : G.Edge), G.tail e = a → G.tail f = b → Nonempty (Walk G.CanFollow e f) := by
  induction p with
  | nil a =>
    intro e f he hf
    exact same_tail_walk G hd e f (he.trans hf.symm)
  | @cons a b c hab rest ih =>
    intro e f he hf
    let ab : G.Edge := ⟨(a, b), hab⟩
    obtain ⟨x, hx, hxa, _⟩ := hd b a a
    let bx : G.Edge := ⟨(b, x), hx⟩
    obtain ⟨p₁⟩ := same_tail_walk G hd e ab he
    have hnext : G.CanFollow ab bx := ⟨rfl, hxa⟩
    obtain ⟨p₂⟩ := ih bx f rfl hf
    exact ⟨p₁.append (Walk.cons hnext p₂)⟩

/-- A finite connected simple graph with minimum degree three has a strongly
connected non-backtracking directed-edge graph. The proof uses a concrete
doubly stochastic flow, including all row and column sum calculations. -/
theorem stronglyConnected (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : StronglyConnected G.Adj) : StronglyConnected G.CanFollow := by
  intro e f
  obtain ⟨p⟩ := hc (G.tail e) (G.tail f)
  exact lift_base_walk G hd p e f rfl rfl

end NB
end NonSymmetricDyson.Full.BulkConnectivity
