import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
The directed-edge convention in Assumption (NB), main-article-1014.tex,
lines 1033–1047. This module models finite simple undirected base graphs.
It does not assert any of the paper's analytic stability theorems.
-/

namespace NonSymmetricDyson.Nonbacktracking

universe u

structure BaseGraph (V : Type u) where
  Adj : V → V → Prop
  symm : ∀ {x y}, Adj x y → Adj y x
  loopless : ∀ x, ¬ Adj x x

namespace BaseGraph

variable {V : Type u} (G : BaseGraph V)

abbrev Edge := {e : V × V // G.Adj e.1 e.2}

def tail (e : G.Edge) : V := e.val.1
def head (e : G.Edge) : V := e.val.2

def reverse (e : G.Edge) : G.Edge :=
  ⟨(e.val.2, e.val.1), G.symm e.property⟩

@[simp] theorem reverse_tail (e : G.Edge) : G.tail (G.reverse e) = G.head e := rfl
@[simp] theorem reverse_head (e : G.Edge) : G.head (G.reverse e) = G.tail e := rfl

@[simp] theorem reverse_reverse (e : G.Edge) : G.reverse (G.reverse e) = e := by
  apply Subtype.ext
  rfl

/-- A transition `(x,y) → (y,w)` is allowed precisely when `w ≠ x`. -/
def CanFollow (e f : G.Edge) : Prop :=
  G.head e = G.tail f ∧ G.head f ≠ G.tail e

theorem canFollow_reverse_iff (e f : G.Edge) :
    G.CanFollow e f ↔ G.CanFollow (G.reverse f) (G.reverse e) := by
  simp only [CanFollow, reverse_head, reverse_tail]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, Ne.symm hn⟩
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, Ne.symm hn⟩

theorem not_canFollow_reverse (e : G.Edge) : ¬ G.CanFollow e (G.reverse e) := by
  simp [CanFollow]

theorem not_canFollow_self (e : G.Edge) : ¬ G.CanFollow e e := by
  intro h
  have hedge : G.Adj (G.tail e) (G.head e) := e.property
  exact G.loopless (G.tail e) (h.1 ▸ hedge)

/-- The unweighted non-backtracking matrix, with entries in `ℝ`. -/
noncomputable def matrix : Matrix G.Edge G.Edge ℝ :=
  by
    classical
    exact fun e f => if G.CanFollow e f then 1 else 0

theorem matrix_nonnegative (e f : G.Edge) : 0 ≤ G.matrix e f := by
  classical
  unfold matrix
  split <;> simp

theorem matrix_reverse_transpose (e f : G.Edge) :
    G.matrix e f = G.matrix (G.reverse f) (G.reverse e) := by
  classical
  simp only [matrix, G.canFollow_reverse_iff e f]

/-- The shift attached to an oriented edge depends on its head, as in (NB). -/
def terminalShift (a : V → ℝ) (e : G.Edge) : ℝ := a (G.head e)

theorem terminalShift_eq_of_head_eq (a : V → ℝ) (e f : G.Edge)
    (h : G.head e = G.head f) :
    G.terminalShift a e = G.terminalShift a f := by
  exact congrArg a h

end BaseGraph

end NonSymmetricDyson.Nonbacktracking
