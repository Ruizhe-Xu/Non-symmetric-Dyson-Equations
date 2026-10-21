import Dyson.Model
import Mathlib

noncomputable section
open scoped BigOperators ComplexConjugate

namespace NonSymmetricDyson.Full.BulkVariance
variable {ι : Type*} [Fintype ι]

theorem complex_norm_sub_sq (w z : ℂ) :
    ‖w - z‖ ^ 2 = ‖w‖ ^ 2 - 2 * (w * conj z).re + ‖z‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact weighted variance identity, with the error measured from an arbitrary
comparison point rather than the row average. -/
theorem weighted_variance (q : ι → ℝ) (hq : ∑ j, q j = 1)
    (w : ι → ℂ) (z : ℂ) :
    (∑ j, q j * ‖w j - z‖ ^ 2) = (∑ j, q j * ‖w j‖ ^ 2) - ‖z‖ ^ 2 +
      2 * ((z - ∑ j, (q j : ℂ) * w j) * conj z).re := by
  simp_rw [complex_norm_sub_sq, mul_add, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hq, one_mul]
  simp only [sub_mul, Complex.sub_re, Finset.sum_mul, Complex.re_sum,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, zero_add, mul_neg, sub_neg_eq_add]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring_nf
  congr 1
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- One row controls both the loss of modulus and the squared edge error.
This is the quantitative convexity step in the phase-Markov proof. -/
theorem row_loss_and_alignment (q : ι → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hrow : ∑ j, q j = 1) (w : ι → ℂ) (z : ℂ) (eps : ℝ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (heps : ‖z - ∑ j, (q j : ℂ) * w j‖ ≤ eps) :
    (∑ j, q j * (1 - ‖w j‖ ^ 2)) ≤ 1 - ‖z‖ ^ 2 + 2 * eps ∧
    (∑ j, q j * ‖w j - z‖ ^ 2) ≤ 1 - ‖z‖ ^ 2 + 2 * eps := by
  let er : ℂ := z - ∑ j, (q j : ℂ) * w j
  have hep : 0 ≤ eps := (norm_nonneg er).trans heps
  have here : |(er * conj z).re| ≤ eps := by
    calc
      |(er * conj z).re| ≤ ‖er * conj z‖ := Complex.abs_re_le_norm _
      _ = ‖er‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ eps * 1 := mul_le_mul heps hz (norm_nonneg z) hep
      _ = eps := mul_one _
  have hsq : (∑ j, q j * ‖w j‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ j, q j * 1 := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (w j), hw j]) (hq j)
      _ = 1 := by simpa using hrow
  have hv := weighted_variance q hrow w z
  have hv0 : 0 ≤ ∑ j, q j * ‖w j - z‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (sq_nonneg _)
  have hreal₁ := (abs_le.mp here).1
  have hreal₂ := (abs_le.mp here).2
  change -(eps) ≤ ((z - ∑ j, (q j : ℂ) * w j) * conj z).re at hreal₁
  change ((z - ∑ j, (q j : ℂ) * w j) * conj z).re ≤ eps at hreal₂
  constructor
  · simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hrow]
    linarith
  · linarith

theorem edge_loss_and_alignment (q : ι → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hrow : ∑ j, q j = 1) (w : ι → ℂ) (z : ℂ) (eps kappa : ℝ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (heps : ‖z - ∑ j, (q j : ℂ) * w j‖ ≤ eps)
    (j : ι) (hk : kappa ≤ q j) (hk0 : 0 < kappa) :
    kappa * (1 - ‖w j‖ ^ 2) ≤ 1 - ‖z‖ ^ 2 + 2 * eps ∧
    kappa * ‖w j - z‖ ^ 2 ≤ 1 - ‖z‖ ^ 2 + 2 * eps := by
  have h := row_loss_and_alignment q hq hrow w z eps hw hz heps
  have hloss (j : ι) : 0 ≤ 1 - ‖w j‖ ^ 2 := by
    nlinarith [norm_nonneg (w j), hw j]
  constructor
  · calc
      _ ≤ q j * (1 - ‖w j‖ ^ 2) := mul_le_mul_of_nonneg_right hk (hloss j)
      _ ≤ ∑ i, q i * (1 - ‖w i‖ ^ 2) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hq i) (hloss i)) (Finset.mem_univ j)
      _ ≤ _ := h.1
  · calc
      _ ≤ q j * ‖w j - z‖ ^ 2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
      _ ≤ ∑ i, q i * ‖w i - z‖ ^ 2 :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hq i) (sq_nonneg ‖w i - z‖)) (Finset.mem_univ j)
      _ ≤ _ := h.2

end NonSymmetricDyson.Full.BulkVariance
