import Dyson.Full.SingularityTopology

noncomputable section
open Filter Set
open scoped Topology

namespace NonSymmetricDyson.Full.Singularities

private theorem interval_endpoint_germ (l r τ : ℝ) (hlr : l < r)
    (hnot : τ ∉ Ioo l r) :
    ∀ᶠ x in 𝓝 τ, x ∈ Ioo l r ↔ (τ = l ∧ τ < x) ∨ (τ = r ∧ x < τ) := by
  by_cases hl : τ = l
  · subst τ
    filter_upwards [Iio_mem_nhds hlr] with x hx
    have hx' : x < r := hx
    simp [hx', ne_of_lt hlr]
  by_cases hr : τ = r
  · subst τ
    filter_upwards [Ioi_mem_nhds hlr] with x hx
    have hx' : l < x := hx
    simp [hx', (ne_of_lt hlr).symm]
  have hout : τ < l ∨ r < τ := by
    by_cases hτl : l < τ
    · right
      have h : r ≤ τ := le_of_not_gt (fun hτr => hnot ⟨hτl, hτr⟩)
      exact lt_of_le_of_ne h (Ne.symm hr)
    · exact Or.inl (lt_of_le_of_ne (le_of_not_gt hτl) hl)
  rcases hout with hout | hout
  · filter_upwards [Iio_mem_nhds hout] with x hx
    have hn : x ∉ Ioo l r := fun h => (not_lt_of_ge h.1.le) hx
    simp [hn, hl, hr]
  · filter_upwards [Ioi_mem_nhds hout] with x hx
    have hn : x ∉ Ioo l r := fun h => (not_lt_of_ge hx.le) h.2
    simp [hn, hl, hr]

private theorem left_endpoint_unique {k : ℕ} (l r : Fin k → ℝ)
    (hlr : ∀ j, l j < r j)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (τ : ℝ) {i j : Fin k} (hi : τ = l i) (hj : τ = l j) : i = j := by
  by_contra hij
  have hd := Set.Ioo_disjoint_Ioo.mp (hdis hij)
  have hp : τ < min (r i) (r j) := lt_min (hi ▸ hlr i) (hj ▸ hlr j)
  rw [← hi, ← hj, max_self] at hd
  exact (not_le_of_gt hp) hd

private theorem right_endpoint_unique {k : ℕ} (l r : Fin k → ℝ)
    (hlr : ∀ j, l j < r j)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (τ : ℝ) {i j : Fin k} (hi : τ = r i) (hj : τ = r j) : i = j := by
  by_contra hij
  have hd := Set.Ioo_disjoint_Ioo.mp (hdis hij)
  have hp : max (l i) (l j) < τ := max_lt (hi ▸ hlr i) (hj ▸ hlr j)
  rw [← hi, ← hj, min_self] at hd
  exact (not_le_of_gt hp) hd

/-- The local one-side/two-side definitions used by the endpoint theorems
are equivalent to the manuscript's one/two incident interval definitions. -/
theorem interval_incidence_iff_support_topology {k : ℕ}
    (l r : Fin k → ℝ) (hlr : ∀ j, l j < r j)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (τ : ℝ) (hτ : τ ∈ frontier (⋃ j, Ioo (l j) (r j))) :
    let T := Finset.univ.filter (fun j => τ = l j ∨ τ = r j)
    (T.card = 1 ↔ IsRegularEdge (⋃ j, Ioo (l j) (r j)) τ) ∧
    (T.card = 2 ↔ IsRegularCusp (⋃ j, Ioo (l j) (r j)) τ) := by
  classical
  let T := Finset.univ.filter (fun j => τ = l j ∨ τ = r j)
  change (T.card = 1 ↔ _) ∧ (T.card = 2 ↔ _)
  have hbounds : 1 ≤ T.card ∧ T.card ≤ 2 :=
    Boundary.finite_intervals_frontier_incidence l r hlr hdis τ hτ
  have hopen : IsOpen (⋃ j, Ioo (l j) (r j)) := isOpen_iUnion fun _ => isOpen_Ioo
  have hnot : τ ∉ ⋃ j, Ioo (l j) (r j) := by
    intro hm
    exact hτ.2 (hopen.interior_eq.symm ▸ hm)
  have hinterval : ∀ᶠ x in 𝓝 τ, ∀ j : Fin k,
      x ∈ Ioo (l j) (r j) ↔ (τ = l j ∧ τ < x) ∨ (τ = r j ∧ x < τ) :=
    eventually_all.mpr fun j => interval_endpoint_germ (l j) (r j) τ (hlr j)
      (fun h => hnot (mem_iUnion.mpr ⟨j, h⟩))
  have hgerm : ∀ᶠ x in 𝓝 τ,
      (x ∈ ⋃ j, Ioo (l j) (r j)) ↔
        ((∃ j, τ = l j) ∧ τ < x) ∨ ((∃ j, τ = r j) ∧ x < τ) := by
    filter_upwards [hinterval] with x hx
    simp only [mem_iUnion, hx, exists_or, exists_and_right]
  have hmem (j : Fin k) : j ∈ T ↔ τ = l j ∨ τ = r j := by simp [T]
  by_cases hleft : ∃ j, τ = l j
  · by_cases hright : ∃ j, τ = r j
    · have hcusp : IsRegularCusp (⋃ j, Ioo (l j) (r j)) τ := by
        filter_upwards [hgerm] with x hx
        rw [hx]
        simp only [hleft, hright, true_and]
        exact ⟨fun h => by rcases h with h | h <;> linarith,
          fun h => by rcases lt_or_gt_of_ne h with h | h; exact Or.inr h; exact Or.inl h⟩
      obtain ⟨i, hi⟩ := hleft
      obtain ⟨j, hj⟩ := hright
      have hij : i ≠ j := by
        intro he
        subst j
        have hh := hlr i
        rw [← hi, ← hj] at hh
        exact (lt_irrefl τ) hh
      have hcard : T.card = 2 := by
        have hh := Finset.one_lt_card.mpr ⟨i, (hmem i).mpr (Or.inl hi),
          j, (hmem j).mpr (Or.inr hj), hij⟩
        omega
      exact ⟨⟨fun h => by omega, fun h => False.elim (cusp_not_edge hcusp h)⟩,
        ⟨fun _ => hcusp, fun _ => hcard⟩⟩
    · have hedge : IsRegularEdge (⋃ j, Ioo (l j) (r j)) τ := by
        refine ⟨-1, by norm_num, ?_⟩
        filter_upwards [hgerm] with x hx
        rw [hx]
        simp only [hleft, hright, true_and, false_and, or_false]
        constructor <;> intro h <;> linarith
      have hcard : T.card = 1 := by
        have hh : T.card ≤ 1 := Finset.card_le_one.mpr (by
          intro i hi j hj
          have hi' := (hmem i).mp hi
          have hj' := (hmem j).mp hj
          exact left_endpoint_unique l r hlr hdis τ
            (hi'.resolve_right (fun h => hright ⟨i, h⟩))
            (hj'.resolve_right (fun h => hright ⟨j, h⟩)))
        omega
      exact ⟨⟨fun _ => hedge, fun _ => hcard⟩,
        ⟨fun h => by omega, fun h => False.elim (edge_not_cusp hedge h)⟩⟩
  · have hright : ∃ j, τ = r j := by
      obtain ⟨j, hj⟩ := Finset.one_le_card.mp hbounds.1
      exact ⟨j, ((hmem j).mp hj).resolve_left (fun h => hleft ⟨j, h⟩)⟩
    have hedge : IsRegularEdge (⋃ j, Ioo (l j) (r j)) τ := by
      refine ⟨1, one_ne_zero, ?_⟩
      filter_upwards [hgerm] with x hx
      rw [hx]
      simp only [hleft, hright, true_and, false_and, false_or, one_mul]
      exact sub_neg.symm
    have hcard : T.card = 1 := by
      have hh : T.card ≤ 1 := Finset.card_le_one.mpr (by
        intro i hi j hj
        have hi' := (hmem i).mp hi
        have hj' := (hmem j).mp hj
        exact right_endpoint_unique l r hlr hdis τ
          (hi'.resolve_left (fun h => hleft ⟨i, h⟩))
          (hj'.resolve_left (fun h => hleft ⟨j, h⟩)))
      omega
    exact ⟨⟨fun _ => hedge, fun _ => hcard⟩,
      ⟨fun h => by omega, fun h => False.elim (edge_not_cusp hedge h)⟩⟩

end NonSymmetricDyson.Full.Singularities
