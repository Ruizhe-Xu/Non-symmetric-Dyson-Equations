import Dyson.Resonance
import Mathlib

namespace NonSymmetricDyson.Full.BulkShortest
open Resonance

variable {V : Type*} {E : V → V → Prop}

def length {a b : V} : Walk E a b → ℕ
  | .nil _ => 0
  | .cons _ p => length p + 1

def vertices {a b : V} : Walk E a b → List V
  | .nil a => [a]
  | @Walk.cons _ _ a _ _ _ p => a :: vertices p

theorem vertices_length {a b : V} (p : Walk E a b) :
    (vertices p).length = length p + 1 := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [vertices, length, ih]

theorem suffix_walk {a b x : V} (p : Walk E a b) (hx : x ∈ vertices p) :
    ∃ q : Walk E x b, (vertices q).Sublist (vertices p) := by
  induction p with
  | nil a =>
    have he : x = a := by simpa [vertices] using hx
    subst x
    exact ⟨Walk.nil a, List.Sublist.refl _⟩
  | @cons a b c h p ih =>
    simp only [vertices, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨Walk.cons h p, List.Sublist.refl _⟩
    · obtain ⟨q, hq⟩ := ih hx
      exact ⟨q, hq.trans (List.sublist_cons_self a (vertices p))⟩

theorem exists_simple_walk {a b : V} (p : Walk E a b) :
    ∃ q : Walk E a b, (vertices q).Nodup := by
  classical
  induction p with
  | nil a => exact ⟨Walk.nil a, by simp [vertices]⟩
  | @cons a b c h p ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases ha : a ∈ vertices q
    · obtain ⟨r, hr⟩ := suffix_walk q ha
      exact ⟨r, hq.sublist hr⟩
    · exact ⟨Walk.cons h q, by simpa [vertices] using And.intro ha hq⟩

/-- Erasing repeated vertices gives the exact finite-dimensional path bound. -/
theorem exists_short_walk [Fintype V] {a b : V} (p : Walk E a b) :
    ∃ q : Walk E a b, length q < Fintype.card V := by
  obtain ⟨q, hq⟩ := exists_simple_walk p
  refine ⟨q, ?_⟩
  have hh := hq.length_le_card
  rw [vertices_length] at hh
  omega

theorem connected_short_walk [Fintype V] (hc : StronglyConnected E) (a b : V) :
    ∃ q : Walk E a b, length q < Fintype.card V := by
  obtain ⟨p⟩ := hc a b
  exact exists_short_walk p

end NonSymmetricDyson.Full.BulkShortest
