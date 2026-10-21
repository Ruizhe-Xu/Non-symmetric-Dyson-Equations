import Dyson.Model
import Dyson.MarkovStability
import Mathlib

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.BulkAlgebra

variable {ι : Type*} [Fintype ι]

def normalizedMarkov (F : Matrix ι ι ℝ) (r : ι → ℝ) (lam : ℝ) : Matrix ι ι ℝ :=
  fun i j => F i j * r j / (lam * r i)

theorem normalizedMarkov_nonnegative (F : Matrix ι ι ℝ) (r : ι → ℝ) (lam : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hr : ∀ i, 0 < r i) (hlam : 0 < lam) :
    ∀ i j, 0 ≤ normalizedMarkov F r lam i j := by
  intro i j
  exact div_nonneg (mul_nonneg (hF i j) (le_of_lt (hr j)))
    (le_of_lt (mul_pos hlam (hr i)))

theorem normalizedMarkov_row_sum (F : Matrix ι ι ℝ) (r : ι → ℝ) (lam : ℝ)
    (hr : ∀ i, 0 < r i) (hlam : 0 < lam)
    (heig : ∀ i, ∑ j, F i j * r j = lam * r i) :
    ∀ i, ∑ j, normalizedMarkov F r lam i j = 1 := by
  intro i
  simp only [normalizedMarkov, ← Finset.sum_div, heig i]
  exact div_self (ne_of_gt (mul_pos hlam (hr i)))

theorem normalizedMarkov_support (F : Matrix ι ι ℝ) (r : ι → ℝ) (lam : ℝ)
    (hr : ∀ i, 0 < r i) (hlam : 0 < lam) (i j : ι) :
    0 < normalizedMarkov F r lam i j ↔ 0 < F i j := by
  unfold normalizedMarkov
  rw [div_pos_iff_of_pos_right (mul_pos hlam (hr i))]
  exact mul_pos_iff_of_pos_right (hr j)

/-- The exact Perron conjugation before any inverse estimate is used. -/
theorem normalizedMarkov_conjugation (F : Matrix ι ι ℝ) (r : ι → ℝ)
    (lam : ℝ) (hr : ∀ i, r i ≠ 0) (hlam : lam ≠ 0)
    (u x : ι → ℂ) (i : ι) :
    (r i : ℂ) * MarkovStability.phaseMarkovOperator
        (normalizedMarkov F r lam) u lam (fun j => x j / (r j : ℂ)) i =
      u i * x i - Model.action F x i := by
  have hri : (r i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr i)
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have hterm (j : ι) :
      ((normalizedMarkov F r lam i j : ℝ) : ℂ) * (x j / (r j : ℂ)) =
        ((F i j : ℂ) * x j) / ((lam : ℂ) * (r i : ℂ)) := by
    have hrj : (r j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr j)
    simp only [normalizedMarkov, Complex.ofReal_div, Complex.ofReal_mul]
    field_simp
  simp only [MarkovStability.phaseMarkovOperator_apply, hterm,
    ← Finset.sum_div, Model.action_apply]
  field_simp

/-- The support-sign criterion directly proves anticommutation. -/
theorem action_anticommutes_of_support (S : Matrix ι ι ℝ) (t : ι → ℂ)
    (ht : ∀ i j, S i j ≠ 0 → t j = -t i) (m : ι → ℂ) (i : ι) :
    Model.action S (fun j => t j * m j) i =
      -t i * Model.action S m i := by
  simp only [Model.action_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : S i j = 0
  · simp [hs]
  · rw [ht i j hs]
    ring

/-- Exact opening identity at a bipartite constant-shift point. -/
theorem bipartite_direction_identity (S : Matrix ι ι ℝ) (t m : ι → ℂ) (z : ℂ)
    (ht : ∀ i j, S i j ≠ 0 → t j = -t i)
    (hm0 : ∀ i, m i ≠ 0)
    (hm : ∀ i, -(m i)⁻¹ = z + Model.action S m i) :
    DysonPaper.Algebra.stabilityAction m (Model.action S) (fun i => t i * m i) =
      fun i => -z * t i * m i ^ 2 := by
  ext i
  rw [DysonPaper.Algebra.stabilityAction, action_anticommutes_of_support S t ht]
  have hact : Model.action S m i = -(m i)⁻¹ - z := by
    linear_combination -hm i
  rw [hact]
  field_simp [hm0 i]
  ring

/-- Diagonal multiplication has the expected upper bound in the actual
finite product norm, used to transfer the Markov estimate back to Dyson. -/
theorem diagonal_upper (q x : ι → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hq : ∀ i, ‖q i‖ ≤ M) :
    ‖fun i => q i * x i‖ ≤ M * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg x))).mpr
  intro i
  rw [norm_mul]
  exact mul_le_mul (hq i) (norm_le_pi_norm x i) (norm_nonneg _) hM

theorem diagonal_lower (q x : ι → ℂ) (b : ℝ)
    (hb : 0 < b) (hq : ∀ i, b ≤ ‖q i‖) :
    b * ‖x‖ ≤ ‖fun i => q i * x i‖ := by
  have hx : ‖x‖ ≤ ‖fun i => q i * x i‖ / b := by
    apply (pi_norm_le_iff_of_nonneg
      (div_nonneg (norm_nonneg _) (le_of_lt hb))).mpr
    intro i
    apply (le_div_iff₀ hb).mpr
    calc
      ‖x i‖ * b ≤ ‖q i‖ * ‖x i‖ := by
        nlinarith [norm_nonneg (x i), hq i]
      _ = ‖q i * x i‖ := (norm_mul _ _).symm
      _ ≤ ‖fun i => q i * x i‖ := norm_le_pi_norm (fun j => q j * x j) i
  have h := (le_div_iff₀ hb).mp hx
  simpa [mul_comm] using h

/-- A positive left vector detects the nonzero linear opening coefficient. -/
theorem left_pairing_square_positive [Nonempty ι] (l q : ι → ℝ)
    (hl : ∀ i, 0 < l i) (hq : ∀ i, 0 < q i) :
    0 < ∑ i, l i * q i ^ 2 := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hl i) (sq_pos_of_pos (hq i))
  · exact Finset.univ_nonempty

end NonSymmetricDyson.Full.BulkAlgebra
