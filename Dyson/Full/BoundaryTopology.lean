import Mathlib

/-! Generic real topology used to pass from local boundary signs to finitely
many intervals. Local sign constancy implies an isolated frontier, and the
compactness argument proving finiteness is internal. Only the standard
classification of bounded open real sets with finite frontier is external.
-/

noncomputable section
open Set
open scoped Topology

namespace NonSymmetricDyson.Full.BoundaryTopology

def OneSidedConstantNear (U : Set ℝ) (τ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    (Ioo (τ-r) τ ⊆ U ∨ Ioo (τ-r) τ ⊆ Uᶜ) ∧
    (Ioo τ (τ+r) ⊆ U ∨ Ioo τ (τ+r) ⊆ Uᶜ)

theorem not_mem_frontier_of_open_subset {U V : Set ℝ} (hV : IsOpen V)
    (hsub : V ⊆ U) {y : ℝ} (hy : y ∈ V) : y ∉ frontier U := by
  intro hf
  exact hf.2 (interior_mono hsub (hV.interior_eq.symm ▸ hy))

theorem not_mem_frontier_of_open_subset_compl {U V : Set ℝ} (hV : IsOpen V)
    (hsub : V ⊆ Uᶜ) {y : ℝ} (hy : y ∈ V) : y ∉ frontier U := by
  simpa only [frontier_compl] using not_mem_frontier_of_open_subset hV hsub hy

theorem isolated_frontier_of_one_sided {U : Set ℝ} {τ : ℝ}
    (h : OneSidedConstantNear U τ) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ frontier U, y ∈ Ioo (τ-r) (τ+r) → y = τ := by
  obtain ⟨r, hr, hl, hright⟩ := h
  refine ⟨r, hr, ?_⟩
  intro y hy hyr
  rcases lt_trichotomy y τ with hlt | heq | hgt
  · have hint : y ∈ Ioo (τ-r) τ := ⟨hyr.1, hlt⟩
    rcases hl with hl | hl
    · exact False.elim (not_mem_frontier_of_open_subset isOpen_Ioo hl hint hy)
    · exact False.elim (not_mem_frontier_of_open_subset_compl isOpen_Ioo hl hint hy)
  · exact heq
  · have hint : y ∈ Ioo τ (τ+r) := ⟨hgt, hyr.2⟩
    rcases hright with hh | hh
    · exact False.elim (not_mem_frontier_of_open_subset isOpen_Ioo hh hint hy)
    · exact False.elim (not_mem_frontier_of_open_subset_compl isOpen_Ioo hh hint hy)

/-- Compactness turns pointwise isolation into a finite set, with no uniform
isolation radius assumed. -/
theorem compact_finite_of_isolated {K : Set ℝ} (hK : IsCompact K)
    (hiso : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ K, y ∈ Ioo (x-r) (x+r) → y = x) : K.Finite := by
  classical
  choose r hr hi using fun x : K => hiso x x.property
  have hcover : K ⊆ ⋃ x : K, Ioo (x.val-r x) (x.val+r x) := by
    intro y hy
    apply mem_iUnion.mpr
    refine ⟨⟨y, hy⟩, ?_⟩
    constructor <;> dsimp <;> linarith [hr ⟨y, hy⟩]
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover
    (fun x : K => Ioo (x.val-r x) (x.val+r x)) (fun _ => isOpen_Ioo) hcover
  apply (T.finite_toSet.image (fun x : K => x.val)).subset
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hT hy)
  exact ⟨x, hx, (hi x y hy hxy).symm⟩

theorem finite_frontier_of_one_sided {U : Set ℝ} {a b : ℝ}
    (hbound : U ⊆ Icc a b)
    (hlocal : ∀ τ ∈ frontier U, OneSidedConstantNear U τ) :
    (frontier U).Finite := by
  have hcompact : IsCompact (frontier U) :=
    isCompact_Icc.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hbound isClosed_Icc))
  exact compact_finite_of_isolated hcompact
    (fun τ hτ => isolated_frontier_of_one_sided (hlocal τ hτ))

/-- A standard theorem about arbitrary open subsets of the real line. No
Dyson functions, algebraic functions, or sign classification occur here. -/
structure ExternalFiniteBoundaryIntervals : Prop where
  intervals : ∀ (U : Set ℝ), IsOpen U →
    (∃ a b : ℝ, U ⊆ Icc a b) → (frontier U).Finite →
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      U = ⋃ i, Ioo (a i) (b i)

/-- The local one-sided sign argument has all the hypotheses required for
the generic real interval classification. Closing the finite union is done
internally, producing the closed spectral bands. -/
theorem finite_open_and_closed_intervals (ext : ExternalFiniteBoundaryIntervals)
    (U : Set ℝ) (hU : IsOpen U) {A B : ℝ} (hbound : U ⊆ Icc A B)
    (hlocal : ∀ τ ∈ frontier U, OneSidedConstantNear U τ) :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      U = ⋃ i, Ioo (a i) (b i) ∧ closure U = ⋃ i, Icc (a i) (b i) := by
  obtain ⟨n, a, b, hab, hdis, heq⟩ := ext.intervals U hU ⟨A, B, hbound⟩
    (finite_frontier_of_one_sided hbound hlocal)
  refine ⟨n, a, b, hab, hdis, heq, ?_⟩
  rw [heq, closure_iUnion_of_finite]
  congr 1
  funext i
  exact closure_Ioo (ne_of_lt (hab i))

end NonSymmetricDyson.Full.BoundaryTopology
