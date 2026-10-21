import Mathlib

/-! The strict bulk really is compact. Separation is written pointwise,
which also handles an empty exceptional set without a convention for its distance. -/

namespace NonSymmetricDyson.Full.StrictBulk

def separated (A : Set ℝ) (ε : ℝ) : Set ℝ :=
  {x | ∀ y ∈ A, ε ≤ |x-y|}

theorem separated_closed (A : Set ℝ) (ε : ℝ) : IsClosed (separated A ε) := by
  have heq : separated A ε = ⋂ y ∈ A, {x : ℝ | ε ≤ |x-y|} := by
    ext x
    simp [separated]
  rw [heq]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (continuous_id.sub continuous_const).abs

theorem separated_frontier_closure_subset (U : Set ℝ) (hU : IsOpen U)
    (ε : ℝ) (hε : 0 < ε) :
    closure U ∩ separated (frontier U) ε ⊆ U := by
  intro x hx
  by_contra hn
  have hxf : x ∈ frontier U := by
    rw [frontier, hU.interior_eq]
    exact ⟨hx.1,hn⟩
  have hh := hx.2 x hxf
  simp only [sub_self, abs_zero] at hh
  linarith

/-- The manuscript's strict bulk is closed and bounded, even if the
regular support has several connected components. -/
theorem strict_bulk_compact (U A : Set ℝ) (hU : IsOpen U)
    (hcompact : IsCompact (closure U)) (ε : ℝ) (hε : 0 < ε) :
    IsCompact (U ∩ separated (frontier U ∪ A) ε) := by
  have heq : U ∩ separated (frontier U ∪ A) ε =
      closure U ∩ separated (frontier U ∪ A) ε := by
    ext x
    constructor
    · intro hx
      exact ⟨subset_closure hx.1,hx.2⟩
    · intro hx
      have hsep : x ∈ separated (frontier U) ε := fun y hy => hx.2 y (Or.inl hy)
      exact ⟨separated_frontier_closure_subset U hU ε hε ⟨hx.1,hsep⟩,hx.2⟩
  rw [heq]
  exact hcompact.inter_right (separated_closed _ _)

end NonSymmetricDyson.Full.StrictBulk
