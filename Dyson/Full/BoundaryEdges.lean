import Dyson.Full.MainDecomposition

noncomputable section
open scoped Topology BigOperators
open Set

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

/-- At a regular frontier point every component density is zero. -/
theorem regular_edge_density_zero {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (regularSupport m i))
    (hτ : τ ∉ singularUnion m) : ∀ j, realDensity m j τ = 0 := by
  intro j
  have hco := family_regularSupport_eq hn algebraic puiseux S a hS hirr m hupper heq i j
  rw [hco] at hfront
  have hopen := family_regularSupport_open algebraic puiseux S a hS m hupper heq j
  have hnmem : τ ∉ regularSupport m j := by
    intro hmem
    exact hfront.2 (hopen.interior_eq.symm ▸ hmem)
  have hnonneg := (family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).2.1 j
  have hzero : (boundaryVector m (τ : ℂ) j).im = 0 := by
    apply le_antisymm _ hnonneg
    exact le_of_not_gt (fun hp => hnmem ⟨hτ, hp⟩)
  simp [realDensity, hzero]

/-- The actual vector boundary value is real at every regular frontier point. -/
theorem regular_frontier_real {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (regularSupport m i))
    (hτ : τ ∉ singularUnion m) : ∀ j, (boundaryVector m (τ : ℂ) j).im = 0 := by
  intro j
  have hh := regular_edge_density_zero hn algebraic puiseux S a hS hirr m hupper heq
    τ i hfront hτ j
  exact (div_eq_zero_iff.mp hh).resolve_right Real.pi_ne_zero

/-- The pairwise comparison also implies the positive-sum comparison used
in the blueprint; the identity contribution is already included in the
irreducibility argument that constructs the pairwise constant. -/
theorem sum_comparison_of_pairwise {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℝ) (β : ℝ) (hβ : 0 < β)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ i j, β * y j ≤ y i) (i : Fin n) :
    (β / n) * ∑ j, y j ≤ y i ∧ y i ≤ ∑ j, y j := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : β * ∑ j, y j ≤ (n : ℝ) * y i := by
    simpa [Finset.mul_sum] using hsum
  constructor
  · apply (mul_le_mul_left hnR).mp
    have hcancel : (n : ℝ) * (β / n) = β := by field_simp
    simpa only [← mul_assoc, hcancel] using hs
  · exact Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)

/-- A frontier point of a finite disjoint union of nonempty open intervals
is incident to exactly one or two intervals. -/
theorem finite_intervals_frontier_incidence {k : ℕ}
    (l r : Fin k → ℝ) (hlr : ∀ j, l j < r j)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (τ : ℝ) (hτ : τ ∈ frontier (⋃ j, Ioo (l j) (r j))) :
    let T := Finset.univ.filter (fun j => τ = l j ∨ τ = r j)
    1 ≤ T.card ∧ T.card ≤ 2 := by
  classical
  dsimp
  have hopen : IsOpen (⋃ j, Ioo (l j) (r j)) := isOpen_iUnion (fun _ => isOpen_Ioo)
  have hnmem : τ ∉ ⋃ j, Ioo (l j) (r j) := by
    intro hm
    exact hτ.2 (hopen.interior_eq.symm ▸ hm)
  have hcl : τ ∈ ⋃ j, Icc (l j) (r j) := by
    have hh := hτ.1
    rw [closure_iUnion_of_finite] at hh
    simpa only [closure_Ioo (ne_of_lt (hlr _))] using hh
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcl
  have hend : τ = l j ∨ τ = r j := by
    by_contra he
    push_neg at he
    exact hnmem (mem_iUnion.mpr ⟨j, lt_of_le_of_ne hj.1 he.1.symm, lt_of_le_of_ne hj.2 he.2⟩)
  constructor
  · exact Finset.one_le_card.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hend⟩⟩
  · have hleft : (Finset.univ.filter (fun j => τ = l j)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hd := Set.Ioo_disjoint_Ioo.mp (hdis hij)
      have hli := (Finset.mem_filter.mp hi).2
      have hlj := (Finset.mem_filter.mp hj).2
      have hp : τ < min (r i) (r j) := lt_min (hli ▸ hlr i) (hlj ▸ hlr j)
      rw [← hli, ← hlj, max_self] at hd
      exact (not_le_of_gt hp) hd
    have hright : (Finset.univ.filter (fun j => τ = r j)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hd := Set.Ioo_disjoint_Ioo.mp (hdis hij)
      have hri := (Finset.mem_filter.mp hi).2
      have hrj := (Finset.mem_filter.mp hj).2
      have hp : max (l i) (l j) < τ := max_lt (hri ▸ hlr i) (hrj ▸ hlr j)
      rw [← hri, ← hrj, min_self] at hd
      exact (not_le_of_gt hp) hd
    rw [Finset.filter_or]
    exact (Finset.card_union_le _ _).trans (by omega)

end NonSymmetricDyson.Full.Boundary
