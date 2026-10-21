import Dyson.Full.BulkShortest
import Dyson.ImaginaryComparability

/-! The shortest-path proof of the corrected polynomial in the revised M3
proof. Positivity is obtained by loop erasure, not Cayley--Hamilton. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.FoundationsPaths
open Manuscript.PositivityCorrection Manuscript.ImaginaryComparability
open Resonance Full.BulkShortest
variable {n : ℕ}

/-- A concrete positive support walk contributes a positive term to the
corresponding matrix power. -/
theorem walk_power_positive (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    {i j : Fin n} (p : Walk (fun i j => 0 < S i j) i j) :
    0 < (S ^ length p) i j := by
  induction p with
  | nil i => simp [length]
  | @cons i j k hij p ih =>
    rw [length, pow_succ', Matrix.mul_apply]
    exact (mul_pos hij ih).trans_le (Finset.single_le_sum
      (fun t _ => mul_nonneg (hS i t) (power_nonnegative S hS _ t k))
      (Finset.mem_univ j))

/-- The source's d−1 bound follows by erasing repeated vertices. -/
theorem short_positive_power (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (i j : Fin n) : ∃ k < n, 0 < (S^k) i j := by
  obtain ⟨p, hp⟩ := connected_short_walk
    (support_stronglyConnected_of_irreducible S hS hirr) i j
  exact ⟨length p, by simpa using hp, walk_power_positive S hS p⟩

/-- Literal polynomial used in revised lines 1535--1541, including the
identity term that supplies the diagonal entries. -/
theorem corrected_polynomial_positive (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∀ i j, 0 < (∑ k ∈ Finset.range n, S^k) i j := by
  intro i j
  obtain ⟨k, hk, hp⟩ := short_positive_power S hS hirr i j
  rw [Matrix.sum_apply]
  exact Finset.sum_pos' (fun t _ => power_nonnegative S hS t i j)
    ⟨k, Finset.mem_range.mpr hk, hp⟩

/-- The finite minimum gives one model-dependent positive lower bound. -/
theorem corrected_polynomial_uniform (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i j, κ ≤ (∑ k ∈ Finset.range n, S^k) i j :=
  exists_positive_entry_lower_bound hn _ (corrected_polynomial_positive S hS hirr)

/-- The actual Dyson imaginary equation is iterated through precisely this
short-path polynomial. The lower modulus q is supplied by the bounded-strip
Dyson estimate, not assumed to compare the imaginary parts. -/
theorem imaginary_parts_comparable (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ),
      0 ≤ z.im → BasicEstimates.IsUpperSolution m →
      BasicEstimates.IsDysonSolution S a z m →
      (∀ i, q ≤ Complex.normSq (m i)) →
      ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  have hB : Nonnegative (q • S) := fun i j => mul_nonneg hq.le (hS i j)
  obtain ⟨κ, hκ, hbound⟩ := corrected_polynomial_uniform hn (q • S) hB
    (irreducible_pos_smul S hirr q hq)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨κ/n, div_pos hκ hnR, ?_⟩
  intro a z m hz hm hsol hmod i
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  simpa only [mul_comm] using power_sum_lower_bound_controls_total (q • S) hB κ hbound
    (fun j => (m j).im) (fun j => (hm j).le)
    (dyson_imaginary_part_supersolution S hS a z hz m hm hsol q hmod) i

end NonSymmetricDyson.Paper.FoundationsPaths
