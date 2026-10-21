import Mathlib.Algebra.Group.Defs

/-!
# Directed-cycle resonance and vertex gauges

This file formalizes the graph-theoretic part of
`lem.zero-set-of-edge-defect` in `main-article-1014.tex` (lines 3299–3410).

The codomain is an arbitrary group. In the paper it is the group of complex
numbers of modulus one, where inverse is complex conjugation. A directed cycle
means a closed directed walk, as in the paper's equation `def.cycle`.

This file does not formalize the compactness argument identifying zero edge
defect (an infimum) with existence of an exact vertex gauge.
-/

namespace NonSymmetricDyson.Resonance

universe u v

variable {V : Type u} {G : Type v}

/-- A finite directed walk. Vertices may repeat. -/
inductive Walk (E : V → V → Prop) : V → V → Type u where
  | nil (a : V) : Walk E a a
  | cons {a b c : V} (edge : E a b) (rest : Walk E b c) : Walk E a c

namespace Walk

variable {E : V → V → Prop}

/-- Concatenation of two directed walks. -/
def append {a b c : V} (p : Walk E a b) (q : Walk E b c) : Walk E a c :=
  match p with
  | nil _ => q
  | cons h r => cons h (append r q)

/-- The ordered product of the weights of source vertices along a walk. -/
def weight [Group G] (phase : V → G) {a b : V} (p : Walk E a b) : G :=
  match p with
  | nil _ => 1
  | @cons _ _ a _ _ _ r => phase a * weight phase r

@[simp] theorem weight_nil [Group G] (phase : V → G) (a : V) :
    weight phase (Walk.nil (E := E) a) = 1 := rfl

@[simp] theorem weight_cons [Group G] (phase : V → G) {a b c : V}
    (h : E a b) (p : Walk E b c) :
    weight phase (Walk.cons h p) = phase a * weight phase p := rfl

/-- Walk weights multiply under concatenation. -/
theorem weight_append [Group G] (phase : V → G) {a b c : V}
    (p : Walk E a b) (q : Walk E b c) :
    weight phase (p.append q) = weight phase p * weight phase q := by
  induction p with
  | nil => simp [append, weight]
  | cons h r ih => simp only [append, weight, ih, mul_assoc]

end Walk

variable {E : V → V → Prop} [Group G]

/-- Every ordered pair of vertices is connected by a directed walk. -/
def StronglyConnected (E : V → V → Prop) : Prop :=
  ∀ a b, Nonempty (Walk E a b)

/-- The product of phases is one around every closed directed walk. -/
def CycleResonant (E : V → V → Prop) (phase : V → G) : Prop :=
  ∀ a (p : Walk E a a), p.weight phase = 1

/-- A vertex gauge represents every source phase as an edge coboundary. -/
def HasVertexGauge (E : V → V → Prop) (phase : V → G) : Prop :=
  ∃ gamma : V → G, ∀ a b, E a b → phase a = (gamma a)⁻¹ * gamma b

/-- A gauge telescopes along every directed walk. -/
theorem weight_eq_gauge (phase gamma : V → G)
    (hgamma : ∀ a b, E a b → phase a = (gamma a)⁻¹ * gamma b)
    {a b : V} (p : Walk E a b) :
    p.weight phase = (gamma a)⁻¹ * gamma b := by
  induction p with
  | nil => simp
  | @cons a b c h r ih =>
      simp only [Walk.weight_cons, hgamma a b h, ih]
      simp [mul_assoc]

/-- Any vertex gauge satisfies all directed-cycle constraints. -/
theorem cycleResonant_of_hasVertexGauge (phase : V → G)
    (h : HasVertexGauge E phase) : CycleResonant E phase := by
  obtain ⟨gamma, hgamma⟩ := h
  intro a p
  rw [weight_eq_gauge phase gamma hgamma p]
  simp

/-- Under the cycle constraint, paths with the same endpoints have the same
weight whenever there is a return path. -/
theorem weight_eq_of_return_path (phase : V → G)
    (hcycle : CycleResonant E phase) {a b : V}
    (p q : Walk E a b) (r : Walk E b a) :
    p.weight phase = q.weight phase := by
  have hp : p.weight phase * r.weight phase = 1 := by
    rw [← Walk.weight_append]
    exact hcycle a (p.append r)
  have hq : q.weight phase * r.weight phase = 1 := by
    rw [← Walk.weight_append]
    exact hcycle a (q.append r)
  exact mul_right_cancel (hp.trans hq.symm)

/-- Strong connectivity makes path weights independent of the chosen path. -/
theorem weight_eq_of_cycleResonant (phase : V → G)
    (hconn : StronglyConnected E) (hcycle : CycleResonant E phase)
    {a b : V} (p q : Walk E a b) :
    p.weight phase = q.weight phase := by
  obtain ⟨r⟩ := hconn b a
  exact weight_eq_of_return_path phase hcycle p q r

/-- The paper's construction: invert the weight of a chosen path to a root. -/
theorem hasVertexGauge_of_cycleResonant (phase : V → G)
    (root : V) (hconn : StronglyConnected E)
    (hcycle : CycleResonant E phase) : HasVertexGauge E phase := by
  classical
  let path (a : V) : Walk E a root := Classical.choice (hconn a root)
  let gamma (a : V) : G := ((path a).weight phase)⁻¹
  refine ⟨gamma, ?_⟩
  intro a b hab
  have hpath : (path a).weight phase = phase a * (path b).weight phase := by
    exact weight_eq_of_cycleResonant phase hconn hcycle (path a)
      (Walk.cons hab (path b))
  change phase a = (((path a).weight phase)⁻¹)⁻¹ * ((path b).weight phase)⁻¹
  rw [inv_inv, hpath]
  simp [mul_assoc]

/-- A strongly connected graph has exactly the phases described by vertex
gauges. This is the algebraic equivalence used in the paper's resonance lemma. -/
theorem cycleResonant_iff_hasVertexGauge (phase : V → G)
    (root : V) (hconn : StronglyConnected E) :
    CycleResonant E phase ↔ HasVertexGauge E phase := by
  constructor
  · exact hasVertexGauge_of_cycleResonant phase root hconn
  · exact cycleResonant_of_hasVertexGauge phase

/-- A gauge can be normalized to equal one at a specified root. -/
theorem hasNormalizedVertexGauge_of_cycleResonant (phase : V → G)
    (root : V) (hconn : StronglyConnected E)
    (hcycle : CycleResonant E phase) :
    ∃ gamma : V → G, gamma root = 1 ∧
      ∀ a b, E a b → phase a = (gamma a)⁻¹ * gamma b := by
  obtain ⟨gamma, hgamma⟩ :=
    hasVertexGauge_of_cycleResonant phase root hconn hcycle
  refine ⟨fun a => (gamma root)⁻¹ * gamma a, ?_, ?_⟩
  · simp
  · intro a b hab
    rw [hgamma a b hab]
    simp [mul_inv_rev, mul_assoc]


end NonSymmetricDyson.Resonance
