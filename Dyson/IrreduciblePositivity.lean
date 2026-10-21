import Dyson.PositivityCorrection
import Dyson.Resonance

set_option autoImplicit false

/-!
# Full corrected positivity theorem and the support-walk bridge

For a nonnegative irreducible real n-by-n matrix, every entry of
`sum_{k=0}^{n-1} A^k` is strictly positive. No short-path hypothesis is
assumed: Cayley–Hamilton proves that vanishing of the first n power entries
forces vanishing of all power entries.
-/

namespace Manuscript.PositivityCorrection

open Polynomial

/-- A scalar entry of the powers of an n-by-n matrix is determined by its
first n values. This is a direct consequence of Cayley–Hamilton. -/
theorem all_power_entries_zero_of_first_entries_zero
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (i j : Fin n) (hzero : ∀ k < n, (A ^ k) i j = 0) (k : ℕ) :
    (A ^ k) i j = 0 := by
  have hchar : A.charpoly ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_one] at hd
    omega
  have hdeg : ((X ^ k : ℝ[X]) %ₘ A.charpoly).natDegree < n := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      Polynomial.natDegree_modByMonic_lt (X ^ k : ℝ[X]) A.charpoly_monic hchar
  rw [A.pow_eq_aeval_mod_charpoly k,
    Polynomial.aeval_eq_sum_range' hdeg A, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Matrix.smul_apply, hzero t (Finset.mem_range.mp ht), smul_zero]

/-- Any positive power entry of a nonnegative n-by-n matrix already
occurs among powers with exponent less than n. -/
theorem exists_short_positive_power
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Nonnegative A)
    (i j : Fin n) (hpos : ∃ k : ℕ, 0 < (A ^ k) i j) :
    ∃ k < n, 0 < (A ^ k) i j := by
  by_contra hshort
  push_neg at hshort
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hzero : ∀ k < n, (A ^ k) i j = 0 := by
    intro k hk
    exact le_antisymm (hshort k hk) (power_nonnegative A hA k i j)
  obtain ⟨k, hk⟩ := hpos
  have hz := all_power_entries_zero_of_first_entries_zero A hn i j hzero k
  rw [hz] at hk
  exact (lt_irrefl 0) hk

/-- The corrected matrix-power sum is entrywise strictly positive under
the exact irreducibility definition stated in the manuscript. -/
theorem irreducible_corrected_power_sum_positive
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Irreducible A) :
    ∀ i j, 0 < (∑ k ∈ Finset.range n, A ^ k) i j := by
  intro i j
  obtain ⟨k, _, hk⟩ := hirr i j
  obtain ⟨t, ht, hpos⟩ := exists_short_positive_power A hA i j ⟨k, hk⟩
  rw [Matrix.sum_apply]
  exact Finset.sum_pos' (fun k _ => power_nonnegative A hA k i j)
    ⟨t, Finset.mem_range.mpr ht, hpos⟩

/-- For distinct endpoints the small positive exponent is nonzero, so it
lies in the manuscript's original range `1,...,n-1`. -/
theorem irreducible_short_positive_powers_off_diagonal
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Irreducible A) :
    ∀ i j, i ≠ j → ∃ k ∈ Finset.Icc 1 (n - 1), 0 < (A ^ k) i j := by
  intro i j hij
  obtain ⟨k, _, hk⟩ := hirr i j
  obtain ⟨t, ht, hpos⟩ := exists_short_positive_power A hA i j ⟨k, hk⟩
  have htpos : 0 < t := by
    by_contra h
    have hzero : t = 0 := by omega
    simp only [hzero, pow_zero, Matrix.one_apply_ne hij] at hpos
    exact (lt_irrefl 0) hpos
  exact ⟨t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpos⟩

/-- The corrected claim in exactly the identity-plus-truncated-sum form. -/
theorem irreducible_identity_add_power_sum_positive
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Irreducible A) :
    ∀ i j, 0 < (1 + PositivePowerSum A) i j :=
  identity_add_power_sum_positive_of_short_positive_powers A hA
    (irreducible_short_positive_powers_off_diagonal A hA hirr)

/-- A positive matrix-power entry gives an actual directed walk in the
support relation; the direction agrees with matrix multiplication. -/
theorem nonempty_support_walk_of_positive_power
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : Nonnegative A)
    (k : ℕ) (i j : Fin n) (hpos : 0 < (A ^ k) i j) :
    Nonempty (NonSymmetricDyson.Resonance.Walk (fun a b => 0 < A a b) i j) := by
  induction k generalizing i j with
  | zero =>
      have hij : i = j := by
        by_contra hne
        simp only [pow_zero, Matrix.one_apply_ne hne] at hpos
        exact (lt_irrefl 0) hpos
      subst j
      exact ⟨NonSymmetricDyson.Resonance.Walk.nil i⟩
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply] at hpos
      have hex : ∃ t : Fin n, 0 < A i t * (A ^ k) t j := by
        by_contra h
        push_neg at h
        have hsum : (∑ t : Fin n, A i t * (A ^ k) t j) ≤ 0 :=
          Finset.sum_nonpos (fun t _ => h t)
        exact (not_lt_of_ge hsum) hpos
      obtain ⟨t, ht⟩ := hex
      have hedge : 0 < A i t := by
        by_contra h
        have hz := mul_nonpos_of_nonpos_of_nonneg
          (le_of_not_gt h) (power_nonnegative A hA k t j)
        exact (not_lt_of_ge hz) ht
      have hrest : 0 < (A ^ k) t j := by
        by_contra h
        have hz := mul_nonpos_of_nonneg_of_nonpos (hA i t) (le_of_not_gt h)
        exact (not_lt_of_ge hz) ht
      obtain ⟨rest⟩ := ih t j hrest
      exact ⟨NonSymmetricDyson.Resonance.Walk.cons hedge rest⟩

/-- Matrix irreducibility implies strong connectivity of the positive-entry
support graph, with no graph assumption added to the manuscript's hypotheses. -/
theorem support_stronglyConnected_of_irreducible
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Irreducible A) :
    NonSymmetricDyson.Resonance.StronglyConnected (fun i j => 0 < A i j) := by
  intro i j
  obtain ⟨k, _, hk⟩ := hirr i j
  exact nonempty_support_walk_of_positive_power A hA k i j hk

end Manuscript.PositivityCorrection
