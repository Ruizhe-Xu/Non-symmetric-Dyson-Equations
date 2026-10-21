import Dyson.Resonance
import Dyson.Nonbacktracking
import Mathlib

/-!
Concrete graph-theoretic arguments used in the bulk chapter.
These lemmas use actual closed walks and group-valued vertex phases.
No paper-specific conclusion is introduced as an axiom.
-/

namespace NonSymmetricDyson.Full.BulkGraph

open Resonance

universe u v
open scoped Classical
variable {V : Type u} {H : Type v} [CommGroup H]
variable {E : V → V → Prop}

/-- A property preserved by every directed edge is preserved by a walk. -/
theorem along_walk {P : V → Prop}
    (step : ∀ a b, E a b → P a → P b)
    {a b : V} (p : Walk E a b) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | @cons a b c hab rest ih => exact ih (step a b hab ha)

/-- The length-two cycle gives the reciprocal relation on a symmetric edge. -/
theorem symmetric_resonance_edge (symm : ∀ a b, E a b → E b a)
    (phase : V → H) (hc : CycleResonant E phase)
    {a b : V} (hab : E a b) : phase a * phase b = 1 := by
  have h := hc a (Walk.cons hab (Walk.cons (symm a b hab) (Walk.nil a)))
  simpa only [Walk.weight_cons, Walk.weight_nil, mul_one] using h

theorem symmetric_resonance_inv (symm : ∀ a b, E a b → E b a)
    (phase : V → H) (hc : CycleResonant E phase)
    {a b : V} (hab : E a b) : phase b = (phase a)⁻¹ := by
  have h := symmetric_resonance_edge symm phase hc hab
  calc
    phase b = (phase a)⁻¹ * (phase a * phase b) := by simp
    _ = (phase a)⁻¹ := by rw [h, mul_one]

/-- A bipartition is expressed directly in terms of the support relation. -/
def IsBipartition (part : Set V) : Prop :=
  ∀ a b, E a b → (a ∈ part ↔ b ∉ part)

/-- Every alternating reciprocal phase on a bipartition is resonant. -/
theorem bipartition_phase_resonant (part : Set V)
    (hp : IsBipartition (E := E) part) (c : H) :
    CycleResonant E (fun a => if a ∈ part then c else c⁻¹) := by
  classical
  apply cycleResonant_of_hasVertexGauge
  refine ⟨fun a => if a ∈ part then 1 else c, ?_⟩
  intro a b hab
  have hflip := hp a b hab
  by_cases ha : a ∈ part
  · have hb : b ∉ part := hflip.mp ha
    simp [ha, hb]
  · have hb : b ∈ part := by
      by_contra hn
      exact ha (hflip.mpr hn)
    simp [ha, hb]

/-- Connectivity forces the alternating reciprocal form in the bipartite case. -/
theorem symmetric_bipartition_classification (symm : ∀ a b, E a b → E b a)
    (root : V) (conn : StronglyConnected E) (part : Set V)
    (hp : IsBipartition (E := E) part) (phase : V → H) :
    CycleResonant E phase ↔
      ∃ c : H, ∀ a, phase a = if a ∈ part then c else c⁻¹ := by
  classical
  constructor
  · intro hc
    let c : H := if root ∈ part then phase root else (phase root)⁻¹
    refine ⟨c, ?_⟩
    intro a
    obtain ⟨p⟩ := conn root a
    have step : ∀ x y, E x y →
        (phase x = if x ∈ part then c else c⁻¹) →
        (phase y = if y ∈ part then c else c⁻¹) := by
      intro x y hxy hx
      have he := symmetric_resonance_inv symm phase hc hxy
      have hflip := hp x y hxy
      by_cases hxp : x ∈ part
      · have hyp : y ∉ part := hflip.mp hxp
        simpa [hxp, hyp, hx] using he
      · have hyp : y ∈ part := by
          by_contra hn
          exact hxp (hflip.mpr hn)
        simpa [hxp, hyp, hx] using he
    apply along_walk step p
    by_cases hr : root ∈ part <;> simp [c, hr]
  · rintro ⟨c, hc⟩
    have heq : phase = fun a => if a ∈ part then c else c⁻¹ := funext hc
    rw [heq]
    exact bipartition_phase_resonant part hp c

/-- A length-one loop forces the phase there to equal one. -/
theorem loop_phase_one (phase : V → H) (hc : CycleResonant E phase)
    {a : V} (haa : E a a) : phase a = 1 := by
  simpa only [Walk.weight_cons, Walk.weight_nil, mul_one] using
    hc a (Walk.cons haa (Walk.nil a))

/-- Once a symmetric resonant phase equals one, connectivity propagates it. -/
theorem all_phases_one_of_one (symm : ∀ a b, E a b → E b a)
    (conn : StronglyConnected E) (phase : V → H) (hc : CycleResonant E phase)
    {root : V} (hr : phase root = 1) : ∀ a, phase a = 1 := by
  intro a
  obtain ⟨p⟩ := conn root a
  apply along_walk (E := E) (P := fun x => phase x = 1) ?_ p hr
  intro x y hxy hx
  simpa [hx] using symmetric_resonance_inv symm phase hc hxy

/-- Along a symmetric walk the phase and its gauge have only two states. -/
theorem gauge_walk_two_states (symm : ∀ a b, E a b → E b a)
    (phase gamma : V → H) (hc : CycleResonant E phase)
    (hg : ∀ a b, E a b → phase a = (gamma a)⁻¹ * gamma b)
    {a b : V} (p : Walk E a b) :
    (phase b = phase a ∧ gamma b = gamma a) ∨
      (phase b = (phase a)⁻¹ ∧ gamma b = gamma a * phase a) := by
  induction p with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons a b c hab rest ih =>
    have hp : phase b = (phase a)⁻¹ := symmetric_resonance_inv symm phase hc hab
    have hgamma : gamma b = gamma a * phase a := by
      rw [hg a b hab]
      simp
    rcases ih with ⟨hp', hg'⟩ | ⟨hp', hg'⟩
    · exact Or.inr ⟨hp'.trans hp, hg'.trans hgamma⟩
    · apply Or.inl
      constructor
      · simpa [hp] using hp'
      · rw [hg', hgamma, hp]
        simp [mul_assoc]

/-- A nontrivial symmetric resonant phase constructs a bipartition.
This proves the non-bipartite classification without importing an odd-cycle
criterion as an additional graph assumption. -/
theorem bipartition_of_nontrivial_resonance
    (symm : ∀ a b, E a b → E b a) (conn : StronglyConnected E)
    (phase : V → H) (hc : CycleResonant E phase)
    (root : V) (hr : phase root ≠ 1) :
    ∃ part : Set V, IsBipartition (E := E) part := by
  classical
  obtain ⟨gamma, hg⟩ := hasVertexGauge_of_cycleResonant phase root conn hc
  have hstates (a : V) :
      (phase a = phase root ∧ gamma a = gamma root) ∨
        (phase a = (phase root)⁻¹ ∧ gamma a = gamma root * phase root) := by
    obtain ⟨p⟩ := conn root a
    exact gauge_walk_two_states symm phase gamma hc hg p
  have hn (a : V) : phase a ≠ 1 := by
    rcases hstates a with ⟨ha, _⟩ | ⟨ha, _⟩
    · simpa [ha] using hr
    · simpa [ha] using hr
  have hdistinct (a b : V) (hab : E a b) : gamma a ≠ gamma b := by
    intro he
    apply hn a
    rw [hg a b hab, he]
    simp
  refine ⟨{a | gamma a = gamma root}, ?_⟩
  intro a b hab
  change gamma a = gamma root ↔ gamma b ≠ gamma root
  constructor
  · intro ha hb
    exact hdistinct a b hab (ha.trans hb.symm)
  · intro hb
    by_contra ha
    have hga : gamma a = gamma root * phase root := by
      rcases hstates a with ⟨_, h⟩ | ⟨_, h⟩
      · exact False.elim (ha h)
      · exact h
    have hgb : gamma b = gamma root * phase root := by
      rcases hstates b with ⟨_, h⟩ | ⟨_, h⟩
      · exact False.elim (hb h)
      · exact h
    exact hdistinct a b hab (hga.trans hgb.symm)

theorem symmetric_nonbipartite_classification
    (symm : ∀ a b, E a b → E b a) (conn : StronglyConnected E)
    (hnobip : ¬ ∃ part : Set V, IsBipartition (E := E) part)
    (phase : V → H) :
    CycleResonant E phase ↔ ∀ a, phase a = 1 := by
  classical
  constructor
  · intro hc a
    by_contra ha
    exact hnobip (bipartition_of_nontrivial_resonance symm conn phase hc a ha)
  · intro ha
    apply cycleResonant_of_hasVertexGauge
    refine ⟨fun _ => 1, ?_⟩
    intro a b hab
    simp [ha a]

namespace NB

open Nonbacktracking

variable (G : BaseGraph V)

/-- The minimum-degree-three condition in a choice-free form.
For a finite simple graph it says that deletion of any two vertices from a
neighbourhood leaves a neighbour. The cardinality equivalence is a separate
finite-set fact, not silently assumed by the theorems below. -/
def HasThreeNeighbors : Prop :=
  ∀ y z₁ z₂, ∃ x, G.Adj y x ∧ x ≠ z₁ ∧ x ≠ z₂

noncomputable def degree [Fintype V] (y : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj y)).card

theorem hasThreeNeighbors_of_degree [Fintype V]
    (hd : ∀ y, 3 ≤ degree G y) : HasThreeNeighbors G := by
  classical
  intro y z₁ z₂
  by_contra h
  have hsub : Finset.univ.filter (G.Adj y) ⊆ {z₁, z₂} := by
    intro x hx
    have ha : G.Adj y x := (Finset.mem_filter.mp hx).2
    by_cases h₁ : x = z₁
    · simp [h₁]
    · have h₂ : x = z₂ := by
        by_contra hn
        exact h ⟨x, ha, h₁, hn⟩
      simp [h₂]
  have hu : (Finset.univ.filter (G.Adj y)).card ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  have hl := hd y
  unfold degree at hl
  omega

theorem degree_of_hasThreeNeighbors [Fintype V]
    (hd : HasThreeNeighbors G) : ∀ y, 3 ≤ degree G y := by
  classical
  intro y
  obtain ⟨x₁, h₁, _, _⟩ := hd y y y
  obtain ⟨x₂, h₂, h₂₁, _⟩ := hd y x₁ x₁
  obtain ⟨x₃, h₃, h₃₁, h₃₂⟩ := hd y x₁ x₂
  have hc : 2 < (Finset.univ.filter (G.Adj y)).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨x₁, x₂, x₃, ?_, ?_, ?_, Ne.symm h₂₁, Ne.symm h₃₁, Ne.symm h₃₂⟩
    · simp [h₁]
    · simp [h₂]
    · simp [h₃]
  change 3 ≤ (Finset.univ.filter (G.Adj y)).card
  omega

theorem hasThreeNeighbors_iff_degree [Fintype V] :
    HasThreeNeighbors G ↔ ∀ y, 3 ≤ degree G y :=
  ⟨degree_of_hasThreeNeighbors G, hasThreeNeighbors_of_degree G⟩

theorem gauge_constant_on_outgoing (deg : HasThreeNeighbors G)
    (phase gamma : G.Edge → H)
    (hg : ∀ e f, G.CanFollow e f → phase e = (gamma e)⁻¹ * gamma f)
    (e f : G.Edge) (ht : G.tail e = G.tail f) : gamma e = gamma f := by
  obtain ⟨x, hx, hxe, hxf⟩ := deg (G.tail e) (G.head e) (G.head f)
  let incoming : G.Edge := ⟨(x, G.tail e), G.symm hx⟩
  have he : G.CanFollow incoming e := ⟨rfl, Ne.symm hxe⟩
  have hf : G.CanFollow incoming f := ⟨ht, Ne.symm hxf⟩
  exact mul_left_cancel ((hg incoming e he).symm.trans (hg incoming f hf))

/-- An edge-indexed gauge descends to vertex potentials under degree three. -/
theorem vertex_potentials_of_edge_gauge (deg : HasThreeNeighbors G)
    (phase : G.Edge → H) (hgauge : HasVertexGauge G.CanFollow phase) :
    ∃ omega : V → H, ∀ e, phase e = (omega (G.tail e))⁻¹ * omega (G.head e) := by
  classical
  obtain ⟨gamma, hg⟩ := hgauge
  let next (y : V) : V := (deg y y y).choose
  have hnext (y : V) : G.Adj y (next y) := (deg y y y).choose_spec.1
  let outgoing (y : V) : G.Edge := ⟨(y, next y), hnext y⟩
  let omega (y : V) : H := gamma (outgoing y)
  have hconstant (e : G.Edge) : gamma e = omega (G.tail e) :=
    gauge_constant_on_outgoing G deg phase gamma hg e (outgoing (G.tail e)) rfl
  refine ⟨omega, ?_⟩
  intro e
  obtain ⟨w, hw, hwe, _⟩ := deg (G.head e) (G.tail e) (G.tail e)
  let f : G.Edge := ⟨(G.head e, w), hw⟩
  have hef : G.CanFollow e f := ⟨rfl, hwe⟩
  rw [hg e f hef, hconstant e, hconstant f]
  rfl

/-- Vertex-potential phases telescope on every closed NB walk. -/
theorem resonance_of_vertex_potentials (omega : V → H) :
    CycleResonant G.CanFollow
      (fun e => (omega (G.tail e))⁻¹ * omega (G.head e)) := by
  apply cycleResonant_of_hasVertexGauge
  refine ⟨fun e => omega (G.tail e), ?_⟩
  intro e f hef
  change (omega (G.tail e))⁻¹ * omega (G.head e) =
    (omega (G.tail e))⁻¹ * omega (G.tail f)
  rw [hef.1]

/-- The full resonance classification once NB strong connectivity is supplied.
The separate connectivity theorem remains a genuine required input; this
statement is not labelled an unconditional proof of that graph theorem. -/
theorem resonance_iff_vertex_potentials (deg : HasThreeNeighbors G)
    (root : G.Edge) (conn : StronglyConnected G.CanFollow)
    (phase : G.Edge → H) :
    CycleResonant G.CanFollow phase ↔
      ∃ omega : V → H, ∀ e,
        phase e = (omega (G.tail e))⁻¹ * omega (G.head e) := by
  constructor
  · intro hc
    exact vertex_potentials_of_edge_gauge G deg phase
      (hasVertexGauge_of_cycleResonant phase root conn hc)
  · rintro ⟨omega, he⟩
    have hfun : phase = fun e =>
        (omega (G.tail e))⁻¹ * omega (G.head e) := funext he
    rw [hfun]
    exact resonance_of_vertex_potentials G omega

theorem resonant_reverse_product (deg : HasThreeNeighbors G)
    (root : G.Edge) (conn : StronglyConnected G.CanFollow)
    (phase : G.Edge → H) (hc : CycleResonant G.CanFollow phase)
    (e : G.Edge) : phase e * phase (G.reverse e) = 1 := by
  obtain ⟨omega, hw⟩ :=
    (resonance_iff_vertex_potentials G deg root conn phase).mp hc
  rw [hw e, hw (G.reverse e)]
  simp only [BaseGraph.reverse_tail, BaseGraph.reverse_head]
  group

end NB
end NonSymmetricDyson.Full.BulkGraph
