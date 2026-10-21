import Dyson.Full.BulkBoundary
import Dyson.Full.BulkTorus

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkQuantitative
open Resonance

theorem unit_square_im (p : Circle) : ‖(p : ℂ) ^ 2 - 1‖ = 2 * |(p : ℂ).im| := by
  have hp : (p : ℂ) * star (p : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', Circle.norm_coe]
    norm_num
  have hid : (p : ℂ) ^ 2 - 1 = (p : ℂ) * ((p : ℂ) - star (p : ℂ)) := by
    linear_combination hp
  have he : (p : ℂ) - star (p : ℂ) = (2 * (p : ℂ).im : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hid, norm_mul, Circle.norm_coe, one_mul, he, norm_mul, Complex.norm_I, mul_one]
  simp [Complex.norm_real, abs_mul]

theorem unit_product_error (p q v w : Circle) (hvw : v * w = 1)
    (delta : ℝ) (hp : ‖(p : ℂ) ^ 2 - (v : ℂ)‖ ≤ delta)
    (hq : ‖(q : ℂ) ^ 2 - (w : ℂ)‖ ≤ delta) :
    |(((p * q : Circle) : ℂ)).im| ≤ delta := by
  have hvw' : (v : ℂ) * (w : ℂ) = 1 := by simpa only [Circle.coe_mul, Circle.coe_one] using congrArg (fun c : Circle => (c : ℂ)) hvw
  have hid : ((p * q : Circle) : ℂ) ^ 2 - 1 =
      ((p : ℂ) ^ 2 - v) * (q : ℂ) ^ 2 + (v : ℂ) * ((q : ℂ) ^ 2 - w) := by
    simp only [Circle.coe_mul]
    linear_combination hvw'
  have hb : ‖((p * q : Circle) : ℂ) ^ 2 - 1‖ ≤ 2 * delta := by
    rw [hid]
    calc
      _ ≤ ‖((p : ℂ) ^ 2 - v) * (q : ℂ) ^ 2‖ +
          ‖(v : ℂ) * ((q : ℂ) ^ 2 - w)‖ := norm_add_le _ _
      _ = ‖(p : ℂ) ^ 2 - v‖ + ‖(q : ℂ) ^ 2 - w‖ := by
        simp [norm_mul, norm_pow, Circle.norm_coe]
      _ ≤ _ := by linarith
  rw [unit_square_im] at hb
  linarith

theorem real_product_error (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (v w : Circle) (hvw : v * w = 1) (delta : ℝ)
    (hxerr : ‖(BulkPhase.normalize x hx : ℂ) ^ 2 - (v : ℂ)‖ ≤ delta)
    (hyerr : ‖(BulkPhase.normalize y hy : ℂ) ^ 2 - (w : ℂ)‖ ≤ delta) :
    |(x * y).im| ≤ ‖x‖ * ‖y‖ * delta := by
  have hh := unit_product_error (BulkPhase.normalize x hx) (BulkPhase.normalize y hy)
    v w hvw delta hxerr hyerr
  have hn (z : ℂ) (hz : z ≠ 0) : (‖z‖ : ℂ) * (BulkPhase.normalize z hz : ℂ) = z := by
    change (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]
  have hid : x * y = ((‖x‖ * ‖y‖ : ℝ) : ℂ) *
      ((BulkPhase.normalize x hx * BulkPhase.normalize y hy : Circle) : ℂ) := by
    rw [Complex.ofReal_mul, Circle.coe_mul]
    calc
      x * y = ((‖x‖ : ℂ) * (BulkPhase.normalize x hx : ℂ)) *
        ((‖y‖ : ℂ) * (BulkPhase.normalize y hy : ℂ)) := congrArg₂ (· * ·) (hn x hx).symm (hn y hy).symm
      _ = _ := by ring
  rw [hid, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
    abs_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y))]
  exact mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg x) (norm_nonneg y))

variable {V : Type*} [Fintype V]

def positivePhase (m : V → ℂ) (hm : ∀ i, m i ≠ 0) : V → Circle :=
  fun i => BulkPhase.normalize (m i) (hm i) ^ 2

/-- The symmetric quantitative phase argument can be done without choosing
angles: take imaginary parts of the polynomial Dyson equation and bound
supported products using their squared phases. -/
theorem symmetric_shift_imag_bound
    (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (v : V → Circle) (hv : CycleResonant (fun i j => S i j ≠ 0) v)
    (delta : ℝ) (hd : 0 ≤ delta)
    (herr : ∀ i, ‖(positivePhase m (BasicEstimates.component_ne_zero hm) i : ℂ) - v i‖ ≤ delta)
    (i : V) :
    |(m i * (z - (a i : ℂ))).im| ≤
      ‖m i‖ * (∑ j, S i j * ‖m j‖) * delta := by
  have hp := PolynomialDyson.of_dyson hsol (BasicEstimates.component_ne_zero hm) i
  have hid : m i * (z - (a i : ℂ)) +
      ∑ j, (S i j : ℂ) * (m i * m j) = -1 := by
    calc
      _ = m i * (z - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -1 := hp.symm
  have him := congrArg Complex.im hid
  simp only [Complex.add_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.neg_im, Complex.one_im, neg_zero] at him
  have hi : (m i * (z - (a i : ℂ))).im = - ∑ j, S i j * (m i * m j).im := by
    simpa only [Complex.mul_im] using (eq_neg_iff_add_eq_zero.mpr him)
  rw [hi, abs_neg]
  calc
    _ ≤ ∑ j, |S i j * (m i * m j).im| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, S i j * (‖m i‖ * ‖m j‖ * delta) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hS i j)]
      by_cases hs : S i j = 0
      · simp [hs]
      · apply mul_le_mul_of_nonneg_left _ (hS i j)
        exact real_product_error (m i) (m j) (BasicEstimates.component_ne_zero hm i)
          (BasicEstimates.component_ne_zero hm j) (v i) (v j)
          (BulkGraph.symmetric_resonance_edge hsymm v hv hs) delta (herr i) (herr j)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A phase-free scalar estimate converts the preceding imaginary-part
bound into the exact rho times spectral-shift quantity used in the paper. -/
theorem shift_bound_of_imaginary_error (z w : ℂ) (a rho c M B delta : ℝ)
    (hrho : 0 ≤ rho) (hc : 0 < c) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hd : 0 ≤ delta) (hz : 0 ≤ z.im)
    (hy : c * rho ≤ w.im) (hn : ‖w‖ ≤ M)
    (herr : |(w * (z - (a : ℂ))).im| ≤ B * delta) :
    c * rho * ‖z - (a : ℂ)‖ ≤ B * delta + (M + c * rho) * z.im := by
  have hre : |z.re - a| * w.im ≤ B * delta + M * z.im := by
    have he : w.im * (z.re - a) = (w * (z - (a : ℂ))).im - w.re * z.im := by
      simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
    have h0 : 0 ≤ w.im := (mul_nonneg hc.le hrho).trans hy
    have hi : |w.im * (z.re - a)| ≤ B * delta + M * z.im := by
      rw [he]
      calc
        _ ≤ |(w * (z - (a : ℂ))).im| + |w.re * z.im| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hz]
          exact add_le_add herr (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm w).trans hn) hz)
    simpa [abs_mul, abs_of_nonneg h0, mul_comm] using hi
  have hzN : ‖z - (a : ℂ)‖ ≤ |z.re - a| + z.im := by
    have h := Complex.norm_le_abs_re_add_abs_im (z - (a : ℂ))
    simpa [Complex.sub_re, Complex.sub_im, abs_of_nonneg hz] using h
  calc
    _ ≤ c * rho * (|z.re - a| + z.im) :=
      mul_le_mul_of_nonneg_left hzN (mul_nonneg hc.le hrho)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg (z.re - a))]

/-- Explicit symmetric physical propagation, with constants depending only
on the modulus/comparability bounds and the row sums of S. -/
theorem symmetric_shift_bound
    (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (rho c M R delta : ℝ) (hrho : 0 ≤ rho) (hc : 0 < c)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hd : 0 ≤ delta) (hz : 0 ≤ z.im)
    (hy : ∀ i, c * rho ≤ (m i).im) (hn : ∀ i, ‖m i‖ ≤ M)
    (hrow : ∀ i, ∑ j, S i j ≤ R)
    (v : V → Circle) (hv : CycleResonant (fun i j => S i j ≠ 0) v)
    (herr : ∀ i, ‖(positivePhase m (BasicEstimates.component_ne_zero hm) i : ℂ) - v i‖ ≤ delta)
    (i : V) :
    c * rho * ‖z - (a i : ℂ)‖ ≤ R * M ^ 2 * delta + (M + c * rho) * z.im := by
  have hi := symmetric_shift_imag_bound S a z m hS hsymm hm hsol v hv delta hd herr i
  have hsum : ∑ j, S i j * ‖m j‖ ≤ R * M := by
    calc
      _ ≤ ∑ j, S i j * M := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hn j) (hS i j)
      _ = (∑ j, S i j) * M := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) hM
  have hsum0 : 0 ≤ ∑ j, S i j * ‖m j‖ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (norm_nonneg _)
  have hprod := mul_le_mul (hn i) hsum hsum0 hM
  have hib : |(m i * (z - (a i : ℂ))).im| ≤ R * M ^ 2 * delta := by
    calc
      _ ≤ ‖m i‖ * (∑ j, S i j * ‖m j‖) * delta := hi
      _ ≤ (M * (R * M)) * delta := mul_le_mul_of_nonneg_right hprod hd
      _ = _ := by ring
  exact shift_bound_of_imaginary_error z (m i) (a i) rho c M (R * M ^ 2) delta
    hrho hc hM (by positivity) hd hz (hy i) (hn i) hib

end NonSymmetricDyson.Full.BulkQuantitative
