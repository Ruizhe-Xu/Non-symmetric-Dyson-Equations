import Mathlib
import Dyson.BasicEstimates

/-! The reducible-matrix remark in the source (lines 858--862).
The only external input is the usual topological ordering of the strongly
connected components of an arbitrary finite directed graph. Matrix zeros,
positive-power irreducibility of diagonal blocks, and the exact recursive
Dyson equations are deduced internally. A singleton with no self-loop is
correctly retained as a zero block, rather than called positive-power
irreducible. The recursive forcing is complex and depends on later blocks;
it is not asserted to be a fixed real shift of the spectral parameter. -/

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.ReducibleBlocks

universe u
variable {V : Type u} [Fintype V]

/-- Pure graph data: the condensation graph has a finite topological order.
The equality criterion makes the fibers the actual strongly connected
components, not an arbitrary partition. -/
structure OrderedComponents (E : V → V → Prop) where
  count : ℕ
  component : V → Fin count
  onto : Function.Surjective component
  edge_mono : ∀ {i j}, E i j → component i ≤ component j
  component_eq : ∀ i j, component i = component j ↔
    Relation.ReflTransGen E i j ∧ Relation.ReflTransGen E j i
  block_paths : ∀ c : Fin count,
    (∀ i j : {v // component v = c},
      Relation.TransGen (fun i j : {v // component v = c} => E i.val j.val) i j) ∨
    (Subsingleton {v // component v = c} ∧
      ∀ i : {v // component v = c}, ¬ E i.val i.val)

/-- Standard finite directed-graph SCC ordering. This statement contains no
matrix, analytic function, or Dyson equation. -/
def ExternalFiniteSCCOrdering : Prop :=
  ∀ (V : Type u) [Fintype V] (E : V → V → Prop), Nonempty (OrderedComponents E)

abbrev Block {E : V → V → Prop} (d : OrderedComponents E) (c : Fin d.count) :=
  {v // d.component v = c}

def blockEquiv {E : V → V → Prop} (d : OrderedComponents E) :
    (Σ c : Fin d.count, Block d c) ≃ V := Equiv.sigmaFiberEquiv d.component

theorem block_nonempty {E : V → V → Prop} (d : OrderedComponents E)
    (c : Fin d.count) : Nonempty (Block d c) := by
  obtain ⟨v, hv⟩ := d.onto c
  exact ⟨⟨v, hv⟩⟩

def diagonalBlock (S : Matrix V V ℝ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (c : Fin d.count) :
    Matrix (Block d c) (Block d c) ℝ := fun i j => S i.val j.val

def blockedMatrix (S : Matrix V V ℝ)
    (d : OrderedComponents (fun i j => 0 < S i j)) :
    Matrix (Σ c, Block d c) (Σ c, Block d c) ℝ :=
  fun i j => S (blockEquiv d i) (blockEquiv d j)

theorem entry_zero_below (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j)) (i j : V)
    (h : d.component j < d.component i) : S i j = 0 := by
  exact le_antisymm (le_of_not_gt (fun hp => (not_le_of_gt h) (d.edge_mono hp)))
    (hS i j)

/-- Reindexing by the component-fiber equivalence is block upper triangular. -/
theorem blockedMatrix_upper_triangular (S : Matrix V V ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j))
    (i j : Σ c, Block d c) (h : j.1 < i.1) : blockedMatrix S d i j = 0 := by
  change S i.2.val j.2.val = 0
  apply entry_zero_below S hS d
  simpa only [i.2.property, j.2.property] using h

private theorem pow_nonnegative [DecidableEq V] (A : Matrix V V ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A^k) i j := by
  induction k with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (ih i t) (hA t j))

/-- Every positive-length support path gives a positive matrix power entry. -/
theorem positive_power_of_path [DecidableEq V] (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {i j : V} (h : Relation.TransGen (fun i j => 0 < A i j) i j) :
    ∃ k : ℕ, 0 < k ∧ 0 < (A^k) i j := by
  induction h with
  | single h => exact ⟨1, by omega, by simpa using h⟩
  | @tail b c hab hbc ih =>
    obtain ⟨k, hk, hpow⟩ := ih
    refine ⟨k+1, by omega, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    exact (mul_pos hpow hbc).trans_le
      (Finset.single_le_sum (fun t _ => mul_nonneg (pow_nonnegative A hA k i t)
        (hA t c)) (Finset.mem_univ b))

/-- The exact diagonal-block alternative under the manuscript's
positive-length definition of irreducibility. The exceptional block is a
nonempty singleton zero matrix. -/
theorem diagonalBlock_irreducible_or_singleton_zero (S : Matrix V V ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j)) (c : Fin d.count) :
    (∀ i j : Block d c, ∃ k : ℕ, 0 < k ∧ 0 < (diagonalBlock S d c ^ k) i j) ∨
    (Nonempty (Block d c) ∧ Subsingleton (Block d c) ∧ diagonalBlock S d c = 0) := by
  rcases d.block_paths c with hp | ⟨hs, hz⟩
  · left
    intro i j
    exact positive_power_of_path (diagonalBlock S d c) (fun i j => hS i.val j.val) (hp i j)
  · right
    refine ⟨block_nonempty d c, hs, ?_⟩
    ext i j
    have hij : i = j := hs.elim i j
    subst j
    exact le_antisymm (le_of_not_gt (hz i)) (hS i.val i.val)

/-- The within-component contribution in the row containing `i`. -/
def diagonalInteraction (S : Matrix V V ℝ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) (i : V) : ℂ :=
  ∑ j : Block d (d.component i), (S i j.val : ℂ) * m j.val

/-- Only strictly later components occur in this forcing term. -/
def laterInteraction (S : Matrix V V ℝ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) (i : V) : ℂ :=
  ∑ j, if d.component i < d.component j then (S i j : ℂ)*m j else 0

theorem action_split (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) (i : V) :
    (∑ j, (S i j : ℂ)*m j) =
      diagonalInteraction S d m i + laterInteraction S d m i := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => d.component j = d.component i)
    (fun j => (S i j : ℂ)*m j)]
  congr 1
  unfold laterInteraction
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => d.component j = d.component i)
    (fun j => if d.component i < d.component j then (S i j : ℂ)*m j else 0)]
  have hz : (∑ j : Block d (d.component i),
      if d.component i < d.component j.val then (S i j.val : ℂ)*m j.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [j.property]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hlt : d.component i < d.component j.val
  · simp [hlt]
  · have hj : d.component j.val < d.component i :=
      lt_of_le_of_ne (le_of_not_gt hlt) j.property
    simp [hlt, entry_zero_below S hS d i j.val hj]

def forcing (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) (i : V) : ℂ :=
  z - (a i : ℂ) + laterInteraction S d m i

/-- The full equation is exactly the collection of diagonal-block equations,
with forcing determined by blocks strictly later in the topological order. -/
theorem dyson_iff_recursive_blocks (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) :
    BasicEstimates.IsDysonSolution S a z m ↔
      ∀ i, -(m i)⁻¹ = forcing S a z d m i + diagonalInteraction S d m i := by
  unfold BasicEstimates.IsDysonSolution forcing
  simp_rw [action_split S hS d m]
  constructor <;> intro h i <;> have hi := h i <;> linear_combination hi

theorem forcing_eq_of_agree_later (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m n : V → ℂ) (i : V)
    (h : ∀ j, d.component i < d.component j → m j = n j) :
    forcing S a z d m i = forcing S a z d n i := by
  unfold forcing laterInteraction
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [h j hj]
  · rfl

theorem forcing_im_ge (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ)
    (hm : BasicEstimates.IsUpperSolution m) (i : V) :
    z.im ≤ (forcing S a z d m i).im := by
  have hnonneg : 0 ≤ (laterInteraction S d m i).im := by
    unfold laterInteraction
    rw [Complex.im_sum]
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · simpa using mul_nonneg (hS i j) (hm j).le
    · simp
  simpa [forcing] using hnonneg

/-- A terminal component has no remaining external block forcing. -/
theorem terminal_forcing (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (d : OrderedComponents (fun i j => 0 < S i j)) (m : V → ℂ) (i : V)
    (hterminal : ∀ j, d.component j ≤ d.component i) :
    forcing S a z d m i = z - (a i : ℂ) := by
  simp only [forcing, laterInteraction]
  have hz : (∑ j, if d.component i < d.component j then
      (S i j : ℂ)*m j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [not_lt_of_ge (hterminal j)]
  rw [hz, add_zero]

/-- Existence of the ordered matrix decomposition, followed by an internally
proved equivalence to the recursive system. No irreducibility is assumed. -/
theorem exists_recursive_block_decomposition (external : ExternalFiniteSCCOrdering.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ d : OrderedComponents (fun i j => 0 < S i j),
      (∀ i j : Σ c, Block d c, j.1 < i.1 → blockedMatrix S d i j = 0) ∧
      (∀ c : Fin d.count,
        (∀ i j : Block d c, ∃ k : ℕ, 0 < k ∧ 0 < (diagonalBlock S d c ^ k) i j) ∨
        (Nonempty (Block d c) ∧ Subsingleton (Block d c) ∧ diagonalBlock S d c = 0)) ∧
      (∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ),
        BasicEstimates.IsDysonSolution S a z m ↔
          ∀ i, -(m i)⁻¹ = forcing S a z d m i + diagonalInteraction S d m i) := by
  obtain ⟨d⟩ := external V (fun i j => 0 < S i j)
  exact ⟨d, blockedMatrix_upper_triangular S hS d,
    diagonalBlock_irreducible_or_singleton_zero S hS d,
    fun a z m => dyson_iff_recursive_blocks S a z hS d m⟩

end NonSymmetricDyson.Full.ReducibleBlocks
