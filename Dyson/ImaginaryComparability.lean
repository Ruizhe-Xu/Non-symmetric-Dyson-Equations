import Dyson.IrreduciblePositivity
import Dyson.BasicEstimates

set_option autoImplicit false

/-!
# Quantitative propagation of imaginary parts

Nonnegative matrix supersolutions propagate to all powers. A lower bound
on the corrected power sum then gives an explicit comparison between each
component and the total mass. The final theorem applies this argument to
the manuscript's actual Dyson equation under a fixed lower bound on the
squared moduli of its solution.
-/

noncomputable section

namespace Manuscript.ImaginaryComparability

open scoped Matrix BigOperators
open Manuscript.PositivityCorrection

/-- Multiplication by an entrywise nonnegative matrix preserves order. -/
theorem mulVec_mono {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Nonnegative B) (u v : Fin n → ℝ) (huv : ∀ i, u i ≤ v i) :
    ∀ i, (B *ᵥ u) i ≤ (B *ᵥ v) i := by
  intro i
  change (∑ j, B i j * u j) ≤ ∑ j, B i j * v j
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hB i j))

/-- A nonnegative supersolution dominates the action of every power. -/
theorem power_mulVec_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Nonnegative B) (y : Fin n → ℝ)
    (hsub : ∀ i, (B *ᵥ y) i ≤ y i) (k : ℕ) :
    ∀ i, ((B ^ k) *ᵥ y) i ≤ y i := by
  induction k with
  | zero => simpa only [pow_zero, Matrix.one_mulVec] using fun i => le_refl (y i)
  | succ k ih =>
      intro i
      have h := (mulVec_mono B hB ((B ^ k) *ᵥ y) y ih i).trans (hsub i)
      simpa only [Matrix.mulVec_mulVec, ← pow_succ'] using h

/-- If every entry of the corrected matrix polynomial is at least `κ`,
then each component controls the total mass with the explicit factor `κ/n`. -/
theorem power_sum_lower_bound_controls_total
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : Nonnegative B)
    (κ : ℝ) (hκ : ∀ i j, κ ≤ (∑ k ∈ Finset.range n, B ^ k) i j)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hsub : ∀ i, (B *ᵥ y) i ≤ y i) (i : Fin n) :
    κ * (∑ j, y j) ≤ (n : ℝ) * y i := by
  have hlow : κ * (∑ j, y j) ≤
      ((∑ k ∈ Finset.range n, B ^ k) *ᵥ y) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hκ i j) (hy j))
  have hupp : ((∑ k ∈ Finset.range n, B ^ k) *ᵥ y) i ≤ (n : ℝ) * y i := by
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    calc
      (∑ k ∈ Finset.range n, ((B ^ k) *ᵥ y) i) ≤
          ∑ _k ∈ Finset.range n, y i :=
        Finset.sum_le_sum (fun k _ => power_mulVec_le B hB y hsub k i)
      _ = (n : ℝ) * y i := by simp
  exact hlow.trans hupp

/-- Every strictly positive finite matrix has a positive common entry bound. -/
theorem exists_positive_entry_lower_bound {n : ℕ} (hn : 0 < n)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 < P i j) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ i j, κ ≤ P i j := by
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_min_image Finset.univ
    (fun p : Fin n × Fin n => P p.1 p.2) hne
  exact ⟨P p.1 p.2, hP p.1 p.2, fun i j => hp (i, j) (Finset.mem_univ _)⟩

/-- A fixed nonnegative irreducible matrix admits one positive comparison
constant for every nonnegative supersolution. The constant is independent
of the supersolution. -/
theorem irreducible_supersolution_comparability
    {n : ℕ} (hn : 0 < n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Nonnegative B) (hirr : Manuscript.PositivityCorrection.Irreducible B) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin n → ℝ,
      (∀ i, 0 ≤ y i) → (∀ i, (B *ᵥ y) i ≤ y i) →
        ∀ i, C * (∑ j, y j) ≤ y i := by
  obtain ⟨κ, hκpos, hκ⟩ := exists_positive_entry_lower_bound hn
    (∑ k ∈ Finset.range n, B ^ k)
    (irreducible_corrected_power_sum_positive B hB hirr)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨κ / n, div_pos hκpos hnR, ?_⟩
  intro y hy hsub i
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  simpa only [mul_comm] using
    power_sum_lower_bound_controls_total B hB κ hκ y hy hsub i

/-- Positive scalar multiplication preserves the manuscript's matrix
irreducibility condition. -/
theorem irreducible_pos_smul {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (q : ℝ) (hq : 0 < q) : Manuscript.PositivityCorrection.Irreducible (q • S) := by
  intro i j
  obtain ⟨k, hk, hpos⟩ := hirr i j
  refine ⟨k, hk, ?_⟩
  simpa only [smul_pow, Matrix.smul_apply, smul_eq_mul] using
    mul_pos (pow_pos hq k) hpos

/-- The exact nonnegative matrix in the weighted imaginary-part equation. -/
def imaginaryTransfer {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (m : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Complex.normSq (m i) * S i j

theorem imaginaryTransfer_nonnegative {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S) (m : Fin n → ℂ) :
    Nonnegative (imaginaryTransfer S m) := by
  intro i j
  exact mul_nonneg (Complex.normSq_nonneg _) (hS i j)

/-- For the exact matrix `B_ij=|m_i|² S_ij`, the imaginary parts satisfy
`B Im m ≤ Im m` whenever `Im z ≥ 0`. -/
theorem dyson_exact_imaginary_transfer_supersolution
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) (z : ℂ) (hz : 0 ≤ z.im) (m : Fin n → ℂ)
    (hm : NonSymmetricDyson.BasicEstimates.IsUpperSolution m)
    (hsol : NonSymmetricDyson.BasicEstimates.IsDysonSolution S a z m) :
    ∀ i, (imaginaryTransfer S m *ᵥ (fun j => (m j).im)) i ≤ (m i).im := by
  intro i
  have hact : (imaginaryTransfer S m *ᵥ (fun j => (m j).im)) i =
      Complex.normSq (m i) * (∑ j, S i j * (m j).im) := by
    simp only [Matrix.mulVec, dotProduct, imaginaryTransfer, Finset.mul_sum, mul_assoc]
  rw [hact]
  calc
    Complex.normSq (m i) * (∑ j, S i j * (m j).im) ≤
        Complex.normSq (m i) * (z.im + ∑ j, S i j * (m j).im) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hz) (Complex.normSq_nonneg _)
    _ = (m i).im :=
      (NonSymmetricDyson.BasicEstimates.weighted_imaginary_part_identity hm hsol i).symm

/-- The exact transfer matrix propagates the Dyson imaginary parts through
every matrix power, rather than only one application of the equation. -/
theorem dyson_exact_imaginary_transfer_powers_le
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (a : Fin n → ℝ) (z : ℂ) (hz : 0 ≤ z.im) (m : Fin n → ℂ)
    (hm : NonSymmetricDyson.BasicEstimates.IsUpperSolution m)
    (hsol : NonSymmetricDyson.BasicEstimates.IsDysonSolution S a z m)
    (k : ℕ) :
    ∀ i, ((imaginaryTransfer S m ^ k) *ᵥ (fun j => (m j).im)) i ≤ (m i).im :=
  power_mulVec_le (imaginaryTransfer S m) (imaginaryTransfer_nonnegative S hS m)
    (fun j => (m j).im)
    (dyson_exact_imaginary_transfer_supersolution S a z hz m hm hsol) k

/-- The imaginary part of an actual upper-half-plane Dyson solution is a
supersolution for `q S` whenever `|m_i|² ≥ q` and `Im z ≥ 0`. -/
theorem dyson_imaginary_part_supersolution
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (a : Fin n → ℝ) (z : ℂ) (hz : 0 ≤ z.im) (m : Fin n → ℂ)
    (hm : NonSymmetricDyson.BasicEstimates.IsUpperSolution m)
    (hsol : NonSymmetricDyson.BasicEstimates.IsDysonSolution S a z m)
    (q : ℝ) (hmod : ∀ i, q ≤ Complex.normSq (m i)) :
    ∀ i, ((q • S) *ᵥ (fun j => (m j).im)) i ≤ (m i).im := by
  intro i
  have hsum : 0 ≤ ∑ j, S i j * (m j).im :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hS i j) (hm j).le)
  have hact : ((q • S) *ᵥ (fun j => (m j).im)) i =
      q * (∑ j, S i j * (m j).im) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
  rw [hact]
  calc
    q * (∑ j, S i j * (m j).im) ≤
        Complex.normSq (m i) * (∑ j, S i j * (m j).im) :=
      mul_le_mul_of_nonneg_right (hmod i) hsum
    _ ≤ Complex.normSq (m i) * (z.im + ∑ j, S i j * (m j).im) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hz) (Complex.normSq_nonneg _)
    _ = (m i).im :=
      (NonSymmetricDyson.BasicEstimates.weighted_imaginary_part_identity hm hsol i).symm

/-- Uniform imaginary-part comparability conditional only on a fixed
positive lower bound `q` for the squared component moduli. The constant
depends on `S`, `q`, and the dimension, and works for every such solution. -/
theorem dyson_imaginary_parts_comparable
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Nonnegative S) (hirr : Manuscript.PositivityCorrection.Irreducible S) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ),
      0 ≤ z.im → NonSymmetricDyson.BasicEstimates.IsUpperSolution m →
      NonSymmetricDyson.BasicEstimates.IsDysonSolution S a z m →
      (∀ i, q ≤ Complex.normSq (m i)) →
        ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  have hB : Nonnegative (q • S) := by
    intro i j
    exact mul_nonneg hq.le (hS i j)
  obtain ⟨C, hC, hcomp⟩ := irreducible_supersolution_comparability hn (q • S)
    hB (irreducible_pos_smul S hirr q hq)
  refine ⟨C, hC, ?_⟩
  intro a z m hz hm hsol hmod i
  exact hcomp (fun j => (m j).im) (fun j => (hm j).le)
    (dyson_imaginary_part_supersolution S hS a z hz m hm hsol q hmod) i

end Manuscript.ImaginaryComparability
