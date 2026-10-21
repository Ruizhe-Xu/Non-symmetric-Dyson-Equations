import Dyson.Full.BulkAlgebra
import Dyson.Full.BulkMarkov
import Dyson.InteriorStability

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkTransfer
variable {V : Type*} [Fintype V]

def scaledMatrix (S : Matrix V V ℝ) (q : V → ℝ) : Matrix V V ℝ :=
  fun i j => q i * S i j * q j

def dysonPhase (m : V → ℂ) (hm : ∀ i, m i ≠ 0) : V → Circle :=
  fun i => ((BulkPhase.normalize (m i) (hm i))⁻¹) ^ 2

theorem dysonPhase_identity (m : V → ℂ) (hm : ∀ i, m i ≠ 0) (i : V) :
    (dysonPhase m hm i : ℂ) * m i ^ 2 = (‖m i‖ : ℂ) ^ 2 := by
  change ((m i / (‖m i‖ : ℂ))⁻¹) ^ 2 * m i ^ 2 = _
  have hn : (‖m i‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hm i))
  field_simp [hm i]

theorem scaledMatrix_nonnegative (S : Matrix V V ℝ) (q : V → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hq : ∀ i, 0 ≤ q i) :
    ∀ i j, 0 ≤ scaledMatrix S q i j := by
  intro i j
  exact mul_nonneg (mul_nonneg (hq i) (hS i j)) (hq j)

theorem scaledMatrix_support (S : Matrix V V ℝ) (q : V → ℝ)
    (hq : ∀ i, 0 < q i) (i j : V) :
    0 < scaledMatrix S q i j ↔ 0 < S i j := by
  unfold scaledMatrix
  rw [mul_pos_iff_of_pos_right (hq j), mul_pos_iff_of_pos_left (hq i)]

/-- Exact diagonal conjugation from the actual Dyson stability matrix to the
phase--Markov matrix, before any inequalities are used. -/
theorem dyson_markov_conjugation
    (S : Matrix V V ℝ) (m u : V → ℂ) (q r : V → ℝ) (lam : ℝ)
    (hq : ∀ i, q i ≠ 0) (hr : ∀ i, r i ≠ 0) (hl : lam ≠ 0)
    (hu : ∀ i, u i * m i ^ 2 = (q i : ℂ) ^ 2) (x : V → ℂ) :
    MarkovStability.phaseMarkovOperator
      (BulkAlgebra.normalizedMarkov (scaledMatrix S q) r lam) u lam
      (fun i => x i / ((q i : ℂ) * (r i : ℂ))) =
    fun i => (u i / ((q i : ℂ) * (r i : ℂ))) *
      InteriorStability.stabilityOperator S m x i := by
  funext i
  have hqi : (q i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hq i)
  have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i)
  have hlc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  have hterm (j : V) :
      ((BulkAlgebra.normalizedMarkov (scaledMatrix S q) r lam i j : ℝ) : ℂ) *
          (x j / ((q j : ℂ) * (r j : ℂ))) =
        (q i : ℂ) / ((lam : ℂ) * (r i : ℂ)) * ((S i j : ℂ) * x j) := by
    have hqj : (q j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hq j)
    have hrj : (r j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr j)
    simp only [BulkAlgebra.normalizedMarkov, scaledMatrix, Complex.ofReal_mul,
      Complex.ofReal_div]
    field_simp
  simp only [MarkovStability.phaseMarkovOperator_apply, hterm, ← Finset.mul_sum,
    InteriorStability.stabilityOperator_apply, Model.action_apply]
  field_simp
  rw [← hu i]
  ring

/-- A lower bound for the phase matrix transfers quantitatively through the
diagonal conjugation. The condition number is exactly the ratio of the largest
and smallest entries of `q*r`. -/
theorem transfer_lower_bound
    (S : Matrix V V ℝ) (m u : V → ℂ) (q r : V → ℝ) (lam : ℝ)
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i) (hl : lam ≠ 0)
    (hu : ∀ i, u i * m i ^ 2 = (q i : ℂ) ^ 2) (hun : ∀ i, ‖u i‖ = 1)
    (b B c : ℝ) (hb : 0 < b) (hB : 0 < B) (hc : 0 ≤ c)
    (hlo : ∀ i, b ≤ q i * r i) (hhi : ∀ i, q i * r i ≤ B)
    (hmarkov : ∀ v : V → ℂ, c * ‖v‖ ≤
      ‖MarkovStability.phaseMarkovOperator
        (BulkAlgebra.normalizedMarkov (scaledMatrix S q) r lam) u lam v‖)
    (x : V → ℂ) :
    (b / B) * c * ‖x‖ ≤ ‖InteriorStability.stabilityOperator S m x‖ := by
  let v : V → ℂ := fun i => x i / ((q i : ℂ) * (r i : ℂ))
  have hvx : (fun i => ((q i : ℂ) * (r i : ℂ)) * v i) = x := by
    funext i
    dsimp [v]
    have hqi : (q i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hq i))
    have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hr i))
    field_simp
  have hnqr (i : V) : ‖(q i : ℂ) * (r i : ℂ)‖ = q i * r i := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hq i), abs_of_pos (hr i)]
  have hxv : ‖x‖ ≤ B * ‖v‖ := by
    have hh := BulkAlgebra.diagonal_upper (fun i => (q i : ℂ) * (r i : ℂ))
      v B (le_of_lt hB) (fun i => by rw [hnqr]; exact hhi i)
    rwa [hvx] at hh
  have hcoef (i : V) : ‖u i / ((q i : ℂ) * (r i : ℂ))‖ ≤ b⁻¹ := by
    rw [norm_div, hun, hnqr, one_div]
    exact inv_anti₀ hb (hlo i)
  have hupper : ‖MarkovStability.phaseMarkovOperator
      (BulkAlgebra.normalizedMarkov (scaledMatrix S q) r lam) u lam v‖ ≤
        b⁻¹ * ‖InteriorStability.stabilityOperator S m x‖ := by
    rw [show v = (fun i => x i / ((q i : ℂ) * (r i : ℂ))) from rfl,
      dyson_markov_conjugation S m u q r lam
        (fun i => ne_of_gt (hq i)) (fun i => ne_of_gt (hr i)) hl hu x]
    exact BulkAlgebra.diagonal_upper _ _ (b⁻¹) (inv_nonneg.mpr (le_of_lt hb)) hcoef
  have hmain := (hmarkov v).trans hupper
  have hcx := mul_le_mul_of_nonneg_left hxv hc
  have hmul := mul_le_mul_of_nonneg_left hmain (le_of_lt hb)
  have hcancel : b * (b⁻¹ * ‖InteriorStability.stabilityOperator S m x‖) =
      ‖InteriorStability.stabilityOperator S m x‖ := by field_simp
  rw [hcancel] at hmul
  have heq : (b / B) * c * ‖x‖ = (b * c * ‖x‖) / B := by ring
  rw [heq]
  apply (div_le_iff₀ hB).mpr
  have hh₁ := mul_le_mul_of_nonneg_left hcx (le_of_lt hb)
  have hh₂ := mul_le_mul_of_nonneg_left hmul (le_of_lt hB)
  nlinarith

end NonSymmetricDyson.Full.BulkTransfer
