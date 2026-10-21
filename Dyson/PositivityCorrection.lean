import Mathlib

set_option autoImplicit false

/-!
# Correction to the truncated-power positivity step

The manuscript claims, in the proofs of `thm.bound` and `lem:F-PF`,
that irreducibility of a nonnegative d-by-d matrix makes
`S + ... + S^(d-1)` strictly positive entrywise. The two-cycle disproves
that claim: reaching a vertex from itself can require d steps.

This file proves the counterexample over the real numbers. It also proves
the elementary repair: adding the identity makes the diagonal positive,
while leaving the already-positive off-diagonal entries positive.
The analytic main theorems of the manuscript are not asserted here.
-/

namespace Manuscript.PositivityCorrection

open scoped Matrix

/-- Entrywise nonnegativity, as used in the manuscript. -/
def Nonnegative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The manuscript's positive-power definition of irreducibility. -/
def Irreducible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ k : ℕ, 1 ≤ k ∧ 0 < (A ^ k) i j

/-- The disputed sum, with exactly the manuscript's limits. -/
def PositivePowerSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ k ∈ Finset.Icc 1 (n - 1), A ^ k

/-- The adjacency matrix of a directed two-cycle. -/
def swap : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem swap_nonnegative : Nonnegative swap := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [swap]

theorem swap_irreducible : Irreducible swap := by
  intro i j
  fin_cases i <;> fin_cases j
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [swap, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨1, by norm_num, ?_⟩
    norm_num [swap]
  · refine ⟨1, by norm_num, ?_⟩
    norm_num [swap]
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [swap, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_truncated_sum : PositivePowerSum swap = swap := by
  simp [PositivePowerSum]

theorem swap_truncated_sum_diagonal_zero :
    (PositivePowerSum swap) 0 0 = 0 := by
  rw [swap_truncated_sum]
  norm_num [swap]

theorem swap_truncated_sum_not_strictly_positive :
    ¬ (∀ i j, 0 < (PositivePowerSum swap) i j) := by
  intro h
  have h00 := h 0 0
  rw [swap_truncated_sum_diagonal_zero] at h00
  exact (lt_irrefl 0) h00

/-- Thus the general implication asserted at the two cited proof steps is false. -/
theorem manuscript_truncated_power_claim_false :
    ¬ (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      Nonnegative A → Irreducible A →
        ∀ i j, 0 < (PositivePowerSum A) i j) := by
  intro h
  exact swap_truncated_sum_not_strictly_positive
    (h swap swap_nonnegative swap_irreducible)

/-- A general algebraic repair, once positivity off the diagonal is known. -/
theorem identity_add_positive_of_off_diagonal_positive
    {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, 0 ≤ P i i)
    (hoff : ∀ i j, i ≠ j → 0 < P i j) :
    ∀ i j, 0 < (1 + P) i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    change 0 < (1 : Matrix (Fin n) (Fin n) ℝ) i i + P i i
    rw [Matrix.one_apply_eq]
    linarith [hdiag i]
  · change 0 < (1 : Matrix (Fin n) (Fin n) ℝ) i j + P i j
    rw [Matrix.one_apply_ne hij, zero_add]
    exact hoff i j hij

theorem power_nonnegative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (k : ℕ) : Nonnegative (A ^ k) := by
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
  | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (ih i t) (hA t j))

theorem positivePowerSum_nonnegative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Nonnegative A) :
    Nonnegative (PositivePowerSum A) := by
  intro i j
  unfold PositivePowerSum
  rw [Matrix.sum_apply]
  exact Finset.sum_nonneg (fun k _ => power_nonnegative A hA k i j)

/-- This isolates precisely the shortest-path input needed for the repair.
It does not silently assume that graph-theoretic input has been proved. -/
theorem identity_add_power_sum_positive_of_short_positive_powers
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Nonnegative A)
    (hshort : ∀ i j, i ≠ j →
      ∃ k ∈ Finset.Icc 1 (n - 1), 0 < (A ^ k) i j) :
    ∀ i j, 0 < (1 + PositivePowerSum A) i j := by
  apply identity_add_positive_of_off_diagonal_positive
  · intro i
    exact positivePowerSum_nonnegative A hA i i
  · intro i j hij
    unfold PositivePowerSum
    rw [Matrix.sum_apply]
    exact Finset.sum_pos'
      (fun k _ => power_nonnegative A hA k i j) (hshort i j hij)

theorem swap_identity_add_strictly_positive :
    ∀ i j, 0 < (1 + PositivePowerSum swap) i j := by
  rw [swap_truncated_sum]
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swap, Matrix.one_apply]

/-- `sum_{k=0}^{d-1} S^k`, the corrected limits, for the same example. -/
theorem swap_corrected_power_sum_strictly_positive :
    ∀ i j, 0 < (∑ k ∈ Finset.range 2, swap ^ k) i j := by
  simpa [swap_truncated_sum, Finset.sum_range_succ] using
    swap_identity_add_strictly_positive

end Manuscript.PositivityCorrection
