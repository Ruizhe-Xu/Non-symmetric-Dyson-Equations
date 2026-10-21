import Dyson.Full.BulkQuantitative
import Dyson.Full.BulkDistance

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkNBQuantitative
open Resonance BulkQuantitative

theorem unit_product_minus_lower (p q : Circle) :
    (p : ℂ).im + (q : ℂ).im ≤ ‖((p * q : Circle) : ℂ) - 1‖ := by
  have hq : star (q : ℂ) * (q : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]
    norm_num
  have he : ((p * q : Circle) : ℂ) - 1 = ((p : ℂ) - star (q : ℂ)) * q := by
    simp only [Circle.coe_mul]
    linear_combination hq
  rw [he, norm_mul, Circle.norm_coe, mul_one]
  have hh := (le_abs_self ((p : ℂ) - star (q : ℂ)).im).trans
    (Complex.abs_im_le_norm ((p : ℂ) - star (q : ℂ)))
  simpa using hh

/-- The upper-half-plane branch is selected quantitatively without choosing
arguments or square roots. -/
theorem unit_product_re_negative (p q : Circle) (s delta : ℝ)
    (hp : s ≤ (p : ℂ).im) (hq : s ≤ (q : ℂ).im)
    (hd : delta < s) (herr : |((p * q : Circle) : ℂ).im| ≤ delta) :
    ((p * q : Circle) : ℂ).re < 0 := by
  by_contra hn
  have hre : 0 ≤ ((p * q : Circle) : ℂ).re := le_of_not_gt hn
  have hplus : 1 ≤ ‖((p * q : Circle) : ℂ) + 1‖ := by
    have h := (le_abs_self (((p * q : Circle) : ℂ) + 1).re).trans
      (Complex.abs_re_le_norm (((p * q : Circle) : ℂ) + 1))
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hid : ‖((p * q : Circle) : ℂ) - 1‖ * ‖((p * q : Circle) : ℂ) + 1‖ =
      2 * |((p * q : Circle) : ℂ).im| := by
    rw [← norm_mul, show (((p * q : Circle) : ℂ) - 1) *
      (((p * q : Circle) : ℂ) + 1) = ((p * q : Circle) : ℂ) ^ 2 - 1 by ring]
    exact unit_square_im (p * q)
  have hminus := unit_product_minus_lower p q
  have hmul := mul_le_mul_of_nonneg_left hplus (norm_nonneg (((p * q : Circle) : ℂ) - 1))
  nlinarith

theorem real_product_re_nonpositive (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (s delta : ℝ)
    (hsx : s ≤ (BulkPhase.normalize x hx : ℂ).im)
    (hsy : s ≤ (BulkPhase.normalize y hy : ℂ).im)
    (hd : delta < s)
    (herr : |((BulkPhase.normalize x hx * BulkPhase.normalize y hy : Circle) : ℂ).im| ≤ delta) :
    (x * y).re ≤ 0 := by
  have hh := unit_product_re_negative (BulkPhase.normalize x hx) (BulkPhase.normalize y hy)
    s delta hsx hsy hd herr
  have he : ((BulkPhase.normalize x hx * BulkPhase.normalize y hy : Circle) : ℂ) =
      (x * y) / ((‖x‖ * ‖y‖ : ℝ) : ℂ) := by
    change x / (‖x‖ : ℂ) * (y / (‖y‖ : ℂ)) = _
    rw [Complex.ofReal_mul]
    ring
  rw [he, Complex.div_ofReal_re] at hh
  have hn : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  exact (neg_of_div_neg_left hh hn.le).le

theorem ratio_imag_bound (X Y Z : ℂ) (A eps : ℝ)
    (hA : 0 ≤ A) (heps : 0 ≤ eps)
    (hX : ‖X‖ ≤ A) (hY : ‖Y‖ ≤ A) (hZ : ‖Z‖ ≤ A)
    (hY1 : 1 ≤ ‖Y‖)
    (hXi : |X.im| ≤ eps) (hYi : |Y.im| ≤ eps) (hZi : |Z.im| ≤ eps) :
    |(X * Z / Y).im| ≤ 3 * A ^ 2 * eps := by
  have hXr := (Complex.abs_re_le_norm X).trans hX
  have hYr := (Complex.abs_re_le_norm Y).trans hY
  have hZr := (Complex.abs_re_le_norm Z).trans hZ
  have hXZi : |(X * Z).im| ≤ 2 * A * eps := by
    rw [Complex.mul_im]
    calc
      _ ≤ |X.re * Z.im| + |X.im * Z.re| := abs_add_le _ _
      _ = |X.re| * |Z.im| + |X.im| * |Z.re| := by simp [abs_mul]
      _ ≤ A * eps + eps * A := add_le_add
        (mul_le_mul hXr hZi (abs_nonneg _) hA)
        (mul_le_mul hXi hZr (abs_nonneg _) heps)
      _ = _ := by ring
  have hXZr : |(X * Z).re| ≤ A ^ 2 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul]
    exact (mul_le_mul hX hZ (norm_nonneg _) hA).trans_eq (by ring)
  have hnum : |(X * Z).im * Y.re - (X * Z).re * Y.im| ≤ 3 * A ^ 2 * eps := by
    calc
      _ ≤ |(X * Z).im * Y.re| + |(X * Z).re * Y.im| := abs_sub _ _
      _ = |(X * Z).im| * |Y.re| + |(X * Z).re| * |Y.im| := by simp [abs_mul]
      _ ≤ (2 * A * eps) * A + A ^ 2 * eps := add_le_add
        (mul_le_mul hXZi hYr (abs_nonneg _) (by positivity))
        (mul_le_mul hXZr hYi (abs_nonneg _) (sq_nonneg A))
      _ = _ := by ring
  have hden : 1 ≤ Complex.normSq Y := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg Y]
  rw [Complex.div_im, ← sub_div, abs_div, abs_of_nonneg (Complex.normSq_nonneg Y)]
  exact (div_le_self (abs_nonneg _) hden).trans hnum


theorem dyson_shift_imag_of_products {I : Type*} [Fintype I]
    (S : Matrix I I ℝ) (a : I → ℝ) (z : ℂ) (m : I → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (eps R : ℝ) (heps : 0 ≤ eps) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hprod : ∀ i j, S i j ≠ 0 → |(m i * m j).im| ≤ eps) (i : I) :
    |(m i * (z - (a i : ℂ))).im| ≤ R * eps := by
  have hp := PolynomialDyson.of_dyson hsol (BasicEstimates.component_ne_zero hm) i
  have hid : m i * (z - (a i : ℂ)) + ∑ j, (S i j : ℂ) * (m i * m j) = -1 := by
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
    _ ≤ ∑ j, S i j * eps := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hS i j)]
      by_cases hs : S i j = 0
      · simp [hs]
      · exact mul_le_mul_of_nonneg_left (hprod i j hs) (hS i j)
    _ = (∑ j, S i j) * eps := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) heps


namespace NB
open Nonbacktracking
variable {V : Type*} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

def vertexH (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (y : V) : ℂ :=
  z - (a y : ℂ) + BulkDyson.NB.outgoingSum G m y

theorem vertexH_eq (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (e : G.Edge) : vertexH G a z m (G.head e) = -(m e)⁻¹ + m (G.reverse e) := by
  rw [vertexH, BulkDyson.NB.outgoingSum_eq, hsol e]
  simp [BaseGraph.terminalShift, add_assoc]

theorem vertexH_product (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (e : G.Edge) : vertexH G a z m (G.head e) * m e = m e * m (G.reverse e) - 1 := by
  rw [vertexH_eq G a z m hsol e]
  field_simp [BasicEstimates.component_ne_zero hm e]
  ring


theorem turn_imag_bound_small
    (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hconn : StronglyConnected G.CanFollow)
    (rho c M delta : ℝ) (hr : 0 < rho) (hc : 0 < c) (hM : 0 < M) (hdel : 0 ≤ delta)
    (hy : ∀ e, c * rho ≤ (m e).im) (hn : ∀ e, ‖m e‖ ≤ M)
    (v : G.Edge → Circle) (hv : CycleResonant G.CanFollow v)
    (herr : ∀ e, ‖(positivePhase m (BasicEstimates.component_ne_zero hm) e : ℂ) - v e‖ ≤ delta)
    (hsmall : delta < c * rho / M)
    (e f : G.Edge) (hef : G.CanFollow e f) :
    |(m e * m f).im| ≤ 3 * (1 + M ^ 2) ^ 2 * M ^ 2 * delta := by
  let eps := M ^ 2 * delta
  let A := 1 + M ^ 2
  have hAn : 0 ≤ A := by dsimp [A]; positivity
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  have hunit (g : G.Edge) :
      |((BulkPhase.normalize (m g) (BasicEstimates.component_ne_zero hm g) *
        BulkPhase.normalize (m (G.reverse g)) (BasicEstimates.component_ne_zero hm (G.reverse g)) : Circle) : ℂ).im| ≤ delta :=
    unit_product_error _ _ (v g) (v (G.reverse g))
      (BulkGraph.NB.resonant_reverse_product G hd root hconn v hv g) delta (herr g) (herr (G.reverse g))
  have hnormphase (g : G.Edge) : c * rho / M ≤
      (BulkPhase.normalize (m g) (BasicEstimates.component_ne_zero hm g) : ℂ).im := by
    change c * rho / M ≤ (m g / (‖m g‖ : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_le_div₀ (hm g).le (hy g)
      (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm g)) (hn g)
  have hrevre (g : G.Edge) : (m g * m (G.reverse g)).re ≤ 0 :=
    real_product_re_nonpositive _ _ (BasicEstimates.component_ne_zero hm g)
      (BasicEstimates.component_ne_zero hm (G.reverse g)) (c * rho / M) delta
      (hnormphase g) (hnormphase (G.reverse g)) hsmall (hunit g)
  have hrevi (g : G.Edge) : |(m g * m (G.reverse g)).im| ≤ eps := by
    have hh := real_product_error _ _ (BasicEstimates.component_ne_zero hm g)
      (BasicEstimates.component_ne_zero hm (G.reverse g)) (v g) (v (G.reverse g))
      (BulkGraph.NB.resonant_reverse_product G hd root hconn v hv g) delta (herr g) (herr (G.reverse g))
    have hprod : ‖m g‖ * ‖m (G.reverse g)‖ ≤ M ^ 2 :=
      (mul_le_mul (hn g) (hn (G.reverse g)) (norm_nonneg _) hM.le).trans_eq (by ring)
    exact hh.trans (mul_le_mul_of_nonneg_right hprod hdel)
  have hprodN (g : G.Edge) : ‖m g * m (G.reverse g) - 1‖ ≤ A := by
    calc
      _ ≤ ‖m g * m (G.reverse g)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ M * M + 1 := by
        rw [norm_mul, norm_one]
        exact add_le_add_right (mul_le_mul (hn g) (hn (G.reverse g)) (norm_nonneg _) hM.le) 1
      _ = _ := by dsimp [A]; ring
  have hprodL (g : G.Edge) : 1 ≤ ‖m g * m (G.reverse g) - 1‖ := by
    have hh := (neg_le_abs ((m g * m (G.reverse g) - 1).re)).trans
      (Complex.abs_re_le_norm (m g * m (G.reverse g) - 1))
    simp only [Complex.sub_re, Complex.one_re] at hh
    linarith [hrevre g]
  let H := vertexH G a z m (G.head e)
  let X := H * m e
  let Y := H * m (G.reverse f)
  let Z := m (G.reverse f) * m f
  have hX : X = m e * m (G.reverse e) - 1 := vertexH_product G a z m hm hsol e
  have hY : Y = m (G.reverse f) * m f - 1 := by
    dsimp [Y, H]
    have heq : G.head e = G.head (G.reverse f) := by simpa using hef.1
    rw [heq, vertexH_product G a z m hm hsol (G.reverse f), G.reverse_reverse]
  have hYi : |Y.im| ≤ eps := by rw [hY]; simpa using hrevi (G.reverse f)
  have hYnorm : ‖Y‖ ≤ A := by rw [hY]; simpa using hprodN (G.reverse f)
  have hYlower : 1 ≤ ‖Y‖ := by rw [hY]; simpa using hprodL (G.reverse f)
  have hY0 : Y ≠ 0 := by intro he; norm_num [he] at hYlower
  have heq : m e * m f = X * Z / Y := by
    apply (eq_div_iff hY0).mpr
    dsimp [X, Y, Z]
    ring
  rw [heq]
  have hh := ratio_imag_bound X Y Z A eps hAn heps
    (by rw [hX]; exact hprodN e) hYnorm
    (by dsimp [Z, A]; rw [norm_mul]; nlinarith [mul_le_mul (hn (G.reverse f)) (hn f) (norm_nonneg _) hM.le])
    hYlower (by rw [hX]; simpa using hrevi e) hYi (by simpa [Z] using hrevi (G.reverse f))
  dsimp [A, eps] at hh
  nlinarith


theorem shift_bound
    (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hconn : StronglyConnected G.CanFollow)
    (rho c M B delta : ℝ) (hr : 0 < rho) (hc : 0 < c) (hM : 0 < M)
    (hB : 0 ≤ B) (hdel : 0 ≤ delta) (hz : 0 ≤ z.im)
    (hy : ∀ e, c * rho ≤ (m e).im) (hn : ∀ e, ‖m e‖ ≤ M)
    (hshift : ∀ y, ‖z - (a y : ℂ)‖ ≤ B)
    (v : G.Edge → Circle) (hv : CycleResonant G.CanFollow v)
    (herr : ∀ e, ‖(positivePhase m (BasicEstimates.component_ne_zero hm) e : ℂ) - v e‖ ≤ delta)
    (y : V) :
    c * rho * ‖z - (a y : ℂ)‖ ≤
      ((Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2 + M * B) * delta +
      (M + c * rho) * z.im := by
  by_cases hs : delta < c * rho / M
  · obtain ⟨x, hxy, _, _⟩ := hd y y y
    let e : G.Edge := ⟨(x,y), G.symm hxy⟩
    have hrow (g : G.Edge) : ∑ f, G.matrix g f ≤ (Fintype.card G.Edge : ℝ) := by
      calc
        _ ≤ ∑ _f : G.Edge, (1 : ℝ) := Finset.sum_le_sum fun f _ => by
          unfold BaseGraph.matrix
          split_ifs <;> norm_num
        _ = _ := by simp
    have ht := dyson_shift_imag_of_products G.matrix (G.terminalShift a) z m
      G.matrix_nonnegative hm hsol (3 * (1 + M ^ 2) ^ 2 * M ^ 2 * delta)
      (Fintype.card G.Edge : ℝ) (by positivity) hrow
      (fun g f hgf => turn_imag_bound_small G a z m hm hsol hd root hconn rho c M delta
        hr hc hM hdel hy hn v hv herr hs g f (by
          by_contra hn
          exact hgf (by simp [BaseGraph.matrix, hn]))) e
    have ht' := shift_bound_of_imaginary_error z (m e) (a y) rho c M
      ((Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2) delta
      hr.le hc hM.le (by positivity) hdel hz (hy e) (hn e)
      (by simpa [BaseGraph.terminalShift, BaseGraph.head, e, mul_assoc] using ht)
    have hnon : 0 ≤ M * B * delta := by positivity
    nlinarith
  · have hs' : c * rho ≤ M * delta := by
      have hh := (div_le_iff₀ hM).mp (le_of_not_gt hs)
      nlinarith
    have hh := mul_le_mul hs' (hshift y) (norm_nonneg _) (by positivity : 0 ≤ M * delta)
    have hnon : 0 ≤ (Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2 * delta := by positivity
    have hnon' : 0 ≤ (M + c * rho) * z.im := by positivity
    nlinarith


end NB
end NonSymmetricDyson.Full.BulkNBQuantitative
