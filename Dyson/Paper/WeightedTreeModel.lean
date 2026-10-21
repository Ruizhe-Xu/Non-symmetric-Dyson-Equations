import Dyson.Paper.TreeWords
import Dyson.Paper.TreeCreation
import Dyson.Paper.TreeSchur

/-! Actual signed-weight type-word Jacobi operators. Every
root and forward branch below is a concrete complex ℓ² space. The block
identities are proved from the checked coordinate formulas. -/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace NonSymmetricDyson.Paper.WeightedTreeModel
open TreeWords
universe u
variable {ι : Type u} [Fintype ι]
variable (S : ι → ι → ℝ) (b : ι → ι → ℝ) (a : ι → ℝ)
variable (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
variable (ha : ∀ i, |a i| ≤ A) (hr : ∀ i, (∑ j : {j : ι // 0 < S i j}, b i j.val^2) ≤ R)

/-- The actual real coupling, retaining its sign. -/
def edgeWeight {i : ι} (w : Word S i) (j : Word.Child w) : ℝ :=
  b (Word.terminal w) j.val

@[simp] theorem edgeWeight_cons {i j : ι} (h : 0 < S i j)
    (w : Word S j) (k : Word.Child w) :
    edgeWeight S b (.cons h w) k = edgeWeight S b w k := rfl

include hr in
theorem edgeWeight_square_bound {i : ι} (w : Word S i) :
    (∑ j : Word.Child w, edgeWeight S b w j^2) ≤ R := hr (Word.terminal w)

abbrev H (i : ι) := TreeOperators.Hilbert (Word S i)

def creation (i : ι) : H S i →L[ℂ] H S i :=
  TreeOperators.creation (Word.treeEquiv S i) (edgeWeight S b) R hR
    (edgeWeight_square_bound S b R hr)

def diagonal (i : ι) : H S i →L[ℂ] H S i :=
  TreeOperators.diagonal (Word.potential a) A hA (fun w => ha (Word.terminal w))

def jacobi (i : ι) : H S i →L[ℂ] H S i :=
  diagonal S a A hA ha i + creation S b R hR hr i +
    (creation S b R hR hr i).adjoint

def root (i : ι) : H S i →L[ℂ] ℂ := TreeOperators.eval (.nil i)

def delta (i : ι) : H S i := TreeOperators.delta (.nil i)

def branch {i j : ι} (h : 0 < S i j) : H S i →L[ℂ] H S j :=
  TreeOperators.restrict (Word.consEmbedding h)

@[simp] theorem root_apply (i : ι) (f : H S i) : root S i f = f (.nil i) := rfl
@[simp] theorem branch_apply {i j : ι} (h : 0 < S i j) (f : H S i) (w : Word S j) :
    branch S h f w = f (.cons h w) := rfl
@[simp] theorem norm_delta (i : ι) : ‖delta S i‖ = 1 := TreeOperators.norm_delta _
@[simp] theorem root_delta (i : ι) : root S i (delta S i) = 1 := by
  simp [root,delta,TreeOperators.delta_apply]
@[simp] theorem branch_delta {i j : ι} (h : 0 < S i j) : branch S h (delta S i) = 0 := by
  ext w
  simp [branch,delta,TreeOperators.delta_apply]
@[simp] theorem inner_delta (i : ι) (f : H S i) : inner ℂ (delta S i) f = root S i f :=
  TreeOperators.inner_delta_left _ _

@[simp] theorem creation_root (i : ι) (f : H S i) :
    creation S b R hR hr i f (.nil i) = 0 := by
  change TreeOperators.creationCoordinates (Word.treeEquiv S i) (edgeWeight S b) f (.nil i) = 0
  rw [← Word.treeEquiv_root S i]
  exact TreeOperators.creationCoordinates_root _ _ _

@[simp] theorem creation_child (i : ι) (f : H S i) (w : Word S i) (j : Word.Child w) :
    creation S b R hR hr i f (Word.child w j) =
      ((edgeWeight S b) w j : ℂ) * f w := by
  change TreeOperators.creationCoordinates (Word.treeEquiv S i) (edgeWeight S b) f (Word.child w j) = _
  rw [← Word.treeEquiv_child S i w j]
  exact TreeOperators.creationCoordinates_child _ _ _ _ _

/-- Prefix deletion intertwines the diagonal potentials exactly. -/
theorem diagonal_branch {i j : ι} (h : 0 < S i j) (f : H S i) :
    branch S h (diagonal S a A hA ha i f) = diagonal S a A hA ha j (branch S h f) := by
  ext w
  simp [diagonal,Word.potential]

/-- The only extra creation term after deleting the root is the coupling
from that root to the root of the selected branch. -/
theorem creation_branch {i j : ι} (h : 0 < S i j) (f : H S i) :
    branch S h (creation S b R hR hr i f) =
      creation S b R hR hr j (branch S h f) +
        root S i f • ((b i j : ℂ) • delta S j) := by
  ext w
  by_cases hw : w = .nil j
  · subst w
    change creation S b R hR hr i f (Word.child (.nil i) ⟨j,h⟩) = _
    simp [creation_child,edgeWeight,Word.terminal,delta,TreeOperators.delta_apply,
      mul_comm]
  · obtain ⟨v,k,rfl⟩ := Word.exists_child w hw
    rw [branch_apply,← Word.child_cons,creation_child]
    simp [creation_child,edgeWeight_cons,branch_apply,delta,TreeOperators.delta_apply,
      Word.child_ne_nil]

/-- The annihilation coordinate formula is an ordinary finite sum over
actual children, already established for the generic ℓ² creation operator. -/
theorem adjoint_apply (i : ι) (f : H S i) (w : Word S i) :
    (creation S b R hR hr i).adjoint f w =
      ∑ j : Word.Child w, ((edgeWeight S b) w j : ℂ) * f (Word.child w j) := by
  simpa [creation] using TreeOperators.creation_adjoint_apply
    (Word.treeEquiv S i) (edgeWeight S b) R hR (edgeWeight_square_bound S b R hr) f w

/-- Annihilation does not acquire any extra term under forward restriction. -/
theorem adjoint_branch {i j : ι} (h : 0 < S i j) (f : H S i) :
    branch S h ((creation S b R hR hr i).adjoint f) =
      (creation S b R hR hr j).adjoint (branch S h f) := by
  ext w
  simp only [branch_apply,adjoint_apply,edgeWeight_cons,Word.child_cons]
  rfl

/-- Root block of the actual Jacobi operator. -/
theorem jacobi_root (i : ι) (f : H S i) :
    root S i (jacobi S b a A R hA hR ha hr i f) =
      (a i : ℂ) * root S i f +
        ∑ j : Word.Child (.nil i), (b i j.val : ℂ) *
          root S j.val (branch S j.property f) := by
  simp [jacobi,root,diagonal,adjoint_apply,Word.potential,Word.terminal,
    edgeWeight,Word.child,creation_root]

/-- Branch block, with the same signed real coupling in both orientations. -/
theorem jacobi_branch {i j : ι} (h : 0 < S i j) (f : H S i) :
    branch S h (jacobi S b a A R hA hR ha hr i f) =
      jacobi S b a A R hA hR ha hr j (branch S h f) +
        root S i f • ((b i j : ℂ) • delta S j) := by
  simp only [jacobi,ContinuousLinearMap.add_apply,map_add,
    diagonal_branch,creation_branch,adjoint_branch]
  abel

/-- The matrix element from the root to an actual child is the signed
coupling itself, not its absolute value. -/
theorem jacobi_child_delta {i j : ι} (h : 0 < S i j) :
    root S j (branch S h (jacobi S b a A R hA hR ha hr i (delta S i))) =
      (b i j : ℂ) := by
  rw [jacobi_branch, branch_delta]
  simp [delta, TreeOperators.delta_apply]


theorem jacobi_selfAdjoint (i : ι) :
    IsSelfAdjoint (jacobi S b a A R hA hR ha hr i) := by
  exact TreeOperators.jacobi_selfAdjoint (Word.treeEquiv S i) (edgeWeight S b) R hR
    (edgeWeight_square_bound S b R hr) (Word.potential a) A hA
    (fun w => ha (Word.terminal w))

theorem norm_jacobi (i : ι) : ‖jacobi S b a A R hA hR ha hr i‖ ≤ A+2*Real.sqrt R := by
  have hd := TreeOperators.norm_diagonal (Word.potential a) A hA
    (fun w : Word S i => ha (Word.terminal w))
  have hb := TreeOperators.norm_creation (Word.treeEquiv S i) (edgeWeight S b) R hR
    (edgeWeight_square_bound S b R hr)
  have ht := norm_add_le (diagonal S a A hA ha i) (creation S b R hR hr i)
  have ht' := norm_add_le (diagonal S a A hA ha i + creation S b R hR hr i)
    (creation S b R hR hr i).adjoint
  have he : ‖(creation S b R hR hr i).adjoint‖ = ‖creation S b R hR hr i‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  change ‖diagonal S a A hA ha i‖ ≤ A at hd
  change ‖creation S b R hR hr i‖ ≤ Real.sqrt R at hb
  dsimp only [jacobi]
  linarith

end NonSymmetricDyson.Paper.WeightedTreeModel
