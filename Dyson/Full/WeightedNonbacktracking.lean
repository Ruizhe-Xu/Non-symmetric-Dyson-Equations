import Dyson.Nonbacktracking
import Dyson.BasicEstimates
import Mathlib

/-! The finite weighted non-backtracking system in the introduction.
The edge weights are actual real Jacobi coefficients and the diagonal shift
is evaluated at the terminal vertex. The conversion from forward recursion
to the vector Dyson equation is proved here. Construction of an infinite-tree
Jacobi operator and identification of its resolvent with these scalar data
are not asserted by this finite algebraic module. -/

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.WeightedNonbacktracking
open Nonbacktracking
variable {V : Type*} [Fintype V] (G : BaseGraph V)

/-- The weight belongs to the outgoing edge, as required by the forward
Schur recursion. The entry is nonnegative even when a Jacobi coefficient is
negative. -/
def matrix (b : V → V → ℝ) : Matrix G.Edge G.Edge ℝ :=
  fun e f => if G.CanFollow e f then (b (G.tail f) (G.head f))^2 else 0

theorem matrix_nonnegative (b : V → V → ℝ) (e f : G.Edge) :
    0 ≤ matrix G b e f := by
  unfold matrix
  split
  · exact sq_nonneg _
  · exact le_rfl

theorem matrix_eq_weight_mul (b : V → V → ℝ) (e f : G.Edge) :
    matrix G b e f = (b (G.tail f) (G.head f))^2 * G.matrix e f := by
  simp only [matrix, BaseGraph.matrix]
  split <;> simp_all

theorem unit_weights : matrix G (fun _ _ => 1) = G.matrix := by
  ext e f
  simp [matrix, BaseGraph.matrix]

theorem positive_iff (b : V → V → ℝ)
    (hb : ∀ x y, G.Adj x y → b x y ≠ 0) (e f : G.Edge) :
    0 < matrix G b e f ↔ G.CanFollow e f := by
  unfold matrix
  split_ifs with h
  · exact iff_of_true (sq_pos_of_ne_zero (hb _ _ f.property)) h
  · simp [h]

/-- The neighbors of the terminal vertex after deleting the backward branch. -/
abbrev ForwardNeighbor (e : G.Edge) :=
  {k : V // G.Adj (G.head e) k ∧ k ≠ G.tail e}

def forwardEdge (e : G.Edge) (k : ForwardNeighbor G e) : G.Edge :=
  ⟨(G.head e, k.val), k.property.1⟩

/-- An actual bijection, so the vertex-neighbor recursion and edge recursion
have identical sums, not just equivalent support predicates. -/
def successorEquiv (e : G.Edge) : {f : G.Edge // G.CanFollow e f} ≃ ForwardNeighbor G e where
  toFun f := ⟨G.head f.val, by
    constructor
    · rw [f.property.1]
      exact f.val.property
    · exact f.property.2⟩
  invFun k := ⟨forwardEdge G e k, rfl, k.property.2⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext f.property.1 rfl
  right_inv k := by
    apply Subtype.ext
    rfl

/-- Matrix action written over precisely the allowed outgoing directed edges. -/
theorem action_eq_successor_sum (b : V → V → ℝ) (m : G.Edge → ℂ) (e : G.Edge) :
    (∑ f, (matrix G b e f : ℂ) * m f) =
      ∑ f ∈ Finset.univ.filter (G.CanFollow e),
        ((b (G.tail f) (G.head f))^2 : ℂ) * m f := by
  simp only [Finset.sum_filter, matrix]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> simp

/-- Exact identification with the sum over k adjacent to h(e), k≠t(e). -/
theorem action_eq_forward_sum (b : V → V → ℝ) (m : G.Edge → ℂ) (e : G.Edge) :
    (∑ f, (matrix G b e f : ℂ) * m f) =
      ∑ k : ForwardNeighbor G e,
        ((b (G.head e) k.val)^2 : ℂ) * m (forwardEdge G e k) := by
  rw [action_eq_successor_sum, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  have h := Equiv.sum_comp (successorEquiv G e)
    (fun k : ForwardNeighbor G e =>
      ((b (G.head e) k.val)^2 : ℂ) * m (forwardEdge G e k))
  rw [← h]
  apply Finset.sum_congr rfl
  intro f _
  have he : forwardEdge G e (successorEquiv G e f) = f.val := by
    apply Subtype.ext
    exact Prod.ext f.property.1 rfl
  rw [he]
  change ((b (G.tail f.val) (G.head f.val))^2 : ℂ) * m f.val =
    ((b (G.head e) (G.head f.val))^2 : ℂ) * m f.val
  rw [f.property.1]

/-- Literal forward scalar recursion. No existence or operator realization is
hidden in this predicate. -/
def IsForwardRecursion (b : V → V → ℝ) (a : V → ℝ) (z : ℂ)
    (m : G.Edge → ℂ) : Prop :=
  ∀ e, -(m e)⁻¹ = z - (a (G.head e) : ℂ) +
    ∑ k : ForwardNeighbor G e,
      ((b (G.head e) k.val)^2 : ℂ) * m (forwardEdge G e k)

theorem forward_recursion_iff_dyson (b : V → V → ℝ) (a : V → ℝ)
    (z : ℂ) (m : G.Edge → ℂ) :
    IsForwardRecursion G b a z m ↔
      BasicEstimates.IsDysonSolution (matrix G b) (G.terminalShift a) z m := by
  simp only [IsForwardRecursion, BasicEstimates.IsDysonSolution,
    BaseGraph.terminalShift, action_eq_forward_sum]

/-- The same identification for row sums, useful for the support-radius
specialization of the finite system. -/
theorem rowSum_eq_forward_sum (b : V → V → ℝ) (e : G.Edge) :
    (∑ f, matrix G b e f) =
      ∑ k : ForwardNeighbor G e, (b (G.head e) k.val)^2 := by
  have h := action_eq_forward_sum G b (fun _ => 1) e
  have hr := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using hr

end NonSymmetricDyson.Full.WeightedNonbacktracking
