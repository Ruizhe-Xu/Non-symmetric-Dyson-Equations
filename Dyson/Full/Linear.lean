import Dyson.InteriorStability
import Dyson.ComponentBounds
import Dyson.Full.Norms
import Mathlib

/-!
Quantitative linear estimates for the actual finite Dyson stability operator.
The norm on a finite function space in this file is the supremum norm.
No boundary values are manufactured by extending the canonical solution by zero.
The intermediate hypotheses below are explicit mathematical data; they are not
advertised as external theorems or as a proof of the whole main stability result.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Linear

open InteriorStability

variable {ι : Type*} [Fintype ι]

/-- A quantitative lower norm bound obtained from an actual positive matrix
weight. The weights and their contraction are hypotheses of this intermediate
lemma; later applications must construct them. -/
theorem weighted_lower_norm_bound
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (w : ι → ℝ)
    (q b B : ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hb : 0 < b) (hB : 0 ≤ B) (hq : q < 1)
    (hwlo : ∀ i, b ≤ w i) (hwhi : ∀ i, w i ≤ B)
    (hw : ∀ i, (∑ j, (‖m i‖ ^ 2 * S i j) * w j) ≤ q * w i)
    (u : ι → ℂ) :
    ‖u‖ ≤ ((‖stabilityOperator S m u‖ / b) / (1 - q)) * B := by
  have hwp : ∀ i, 0 < w i := fun i => hb.trans_le (hwlo i)
  have hf : ∀ i, ‖stabilityOperator S m u i‖ ≤
      (‖stabilityOperator S m u‖ / b) * w i := by
    intro i
    calc
      ‖stabilityOperator S m u i‖ ≤ ‖stabilityOperator S m u‖ :=
        norm_le_pi_norm _ i
      _ = (‖stabilityOperator S m u‖ / b) * b :=
        (div_mul_cancel₀ _ hb.ne').symm
      _ ≤ (‖stabilityOperator S m u‖ / b) * w i :=
        mul_le_mul_of_nonneg_left (hwlo i) (div_nonneg (norm_nonneg _) hb.le)
  have hh := UniquenessAux.bound_of_weighted_contraction
    (fun i j => ‖m i‖ ^ 2 * S i j) w (fun i => ‖u i‖)
    (fun i => ‖stabilityOperator S m u i‖) q
    (‖stabilityOperator S m u‖ / b)
    (fun i j => mul_nonneg (sq_nonneg _) (hS i j)) hwp
    (fun i => norm_nonneg _) hq
    (fun i => by simpa only [add_comm] using stability_norm_majorant hS u i)
    hw hf
  have hc : 0 ≤ (‖stabilityOperator S m u‖ / b) / (1 - q) :=
    div_nonneg (div_nonneg (norm_nonneg _) hb.le) (sub_pos.mpr hq).le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc hB)).mpr
  intro i
  exact (hh i).trans (mul_le_mul_of_nonneg_left (hwhi i) hc)

/-- Row-sum version of the positive-weight estimate. -/
theorem row_lower_norm_bound
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (q : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hq : q < 1)
    (hrow : ∀ i, ‖m i‖ ^ 2 * ∑ j, S i j ≤ q)
    (u : ι → ℂ) :
    ‖u‖ ≤ ‖stabilityOperator S m u‖ / (1 - q) := by
  have hh := weighted_lower_norm_bound S m (fun _ => 1) q 1 1 hS
    (by norm_num) (by norm_num) hq (fun _ => le_rfl) (fun _ => le_rfl)
    (fun i => by simpa [Finset.mul_sum] using hrow i) u
  simpa using hh

/-- The row bound proves invertibility without presupposing the existence
of an upper-half-plane solution. -/
theorem bijective_of_row_bound
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (q : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hq : q < 1)
    (hrow : ∀ i, ‖m i‖ ^ 2 * ∑ j, S i j ≤ q) :
    Function.Bijective (stabilityOperator S m) := by
  have hker : ∀ u, stabilityOperator S m u = 0 → u = 0 := by
    intro u hu
    have hh := row_lower_norm_bound S m q hS hq hrow u
    rw [hu, norm_zero, zero_div] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  have hinj : Function.Injective (stabilityOperator S m) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, huv, sub_self]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Uniform high-height stability, derived from the actual Dyson solution.
The bound 2 is independent of the point and the solution. -/
theorem high_height_lower_norm_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hrow : ∀ i, 2 * ∑ j, S i j ≤ z.im ^ 2)
    (u : ι → ℂ) : ‖u‖ ≤ 2 * ‖stabilityOperator S m u‖ := by
  have hsmall : ∀ i, ‖m i‖ ^ 2 * ∑ j, S i j ≤ 1 / 2 := by
    intro i
    have hn := BasicEstimates.rough_bound hS hz hm hsol i
    have hp : 0 ≤ ∑ j, S i j := Finset.sum_nonneg fun j _ => hS i j
    have hmn : 0 ≤ ‖m i‖ := norm_nonneg _
    have hprod : ‖m i‖ * z.im ≤ 1 := by
      exact (le_div_iff₀ hz).mp (by simpa only [one_div] using hn)
    have hsquare : ‖m i‖ ^ 2 * z.im ^ 2 ≤ 1 := by
      have hx : 0 ≤ 1 + ‖m i‖ * z.im := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hx]
    have hrowmul := mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg ‖m i‖)
    nlinarith
  have hh := row_lower_norm_bound S m (1 / 2) hS (by norm_num) hsmall u
  norm_num at hh ⊢
  linarith

/-- Quantitative interior stability from a genuine component lower bound.
This is useful on compact middle-height rectangles and does not assume any
spectral gap estimate. -/
theorem interior_lower_norm_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (b h : ℝ) (hS : ∀ i j, 0 ≤ S i j) (hh : 0 < h)
    (hz : h ≤ z.im) (hb : 0 < b)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hlo : ∀ i, b ≤ ‖m i‖) (u : ι → ℂ) :
    ‖u‖ ≤ (1 / (h ^ 2 * b ^ 2)) * ‖stabilityOperator S m u‖ := by
  have hzp : 0 < z.im := hh.trans_le hz
  let C := ‖stabilityOperator S m u‖ / (h * b ^ 2)
  have hden : 0 < h * b ^ 2 := mul_pos hh (sq_pos_of_pos hb)
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) hden.le
  have hforcing : ∀ i, ‖stabilityOperator S m u i‖ ≤ C * z.im * ‖m i‖ ^ 2 := by
    intro i
    have hs : b ^ 2 ≤ ‖m i‖ ^ 2 := pow_le_pow_left₀ hb.le (hlo i) 2
    calc
      ‖stabilityOperator S m u i‖ ≤ ‖stabilityOperator S m u‖ := norm_le_pi_norm _ i
      _ = C * (h * b ^ 2) := (div_mul_cancel₀ _ hden.ne').symm
      _ ≤ C * (z.im * ‖m i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hz hs (sq_nonneg _) hzp.le) hC
      _ = _ := by ring
  have hw := weighted_stability_estimate hS hzp hm hsol u C hforcing
  have hbound : ∀ i, ‖u i‖ ≤ C / h := by
    intro i
    calc
      ‖u i‖ ≤ C * (m i).im := hw i
      _ ≤ C * ‖m i‖ := mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hC
      _ ≤ C * z.im⁻¹ :=
        mul_le_mul_of_nonneg_left (BasicEstimates.rough_bound hS hzp hm hsol i) hC
      _ ≤ C * h⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hh hz) hC
      _ = _ := div_eq_mul_inv _ _ |>.symm
  have hn : ‖u‖ ≤ C / h :=
    (pi_norm_le_iff_of_nonneg (div_nonneg hC hh.le)).mpr hbound
  calc
    ‖u‖ ≤ C / h := hn
    _ = _ := by dsimp [C]; ring

/-- An explicit uniform bound for every solution in a middle-height rectangle.
The compactness step in the manuscript is replaced by a stronger direct bound. -/
theorem middle_rectangle_lower_norm_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (T h H : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hT : 0 ≤ T) (hh : 0 < h) (hH : h ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : ι → ℂ),
      |z.re| ≤ T → h ≤ z.im → z.im ≤ H →
      BasicEstimates.IsUpperSolution m → BasicEstimates.IsDysonSolution S a z m →
      ∀ u, ‖u‖ ≤ C * ‖stabilityOperator S m u‖ := by
  let b := ComponentBounds.uniformLowerConstant S a h⁻¹ / (1 + T + H)
  have hc := ComponentBounds.uniformLowerConstant_pos (a := a) hS
    (inv_pos.mpr hh).le
  have hd : 0 < 1 + T + H := by linarith
  have hb : 0 < b := div_pos hc hd
  refine ⟨1 / (h ^ 2 * b ^ 2), by positivity, ?_⟩
  intro z m hreal hheight hhigh hm hsol u
  have hz : 0 < z.im := hh.trans_le hheight
  have hupper : ∀ i, ‖m i‖ ≤ h⁻¹ := fun i =>
    (BasicEstimates.rough_bound hS hz hm hsol i).trans (inv_anti₀ hh hheight)
  have hzn : ‖z‖ ≤ T + H := by
    have hc := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at hc
    linarith
  apply interior_lower_norm_bound S a z m b h hS hh hheight hb hm hsol
  intro i
  calc
    b ≤ ComponentBounds.uniformLowerConstant S a h⁻¹ / (1 + ‖z‖) := by
      exact div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
    _ ≤ ‖m i‖ := ComponentBounds.common_scaled_lower_bound hS hm hsol
      (inv_pos.mpr hh).le hupper i

/-- The exact positive derivative weight used off the support yields a
quantitative contraction. In applications `w` is the real Stieltjes
derivative; its existence is not assumed to be a Dyson conclusion. -/
theorem derivative_weight_contraction
    (S : Matrix ι ι ℝ) (m w : ι → ℝ) (c : ℝ)
    (hid : ∀ i, w i - m i ^ 2 * ∑ j, S i j * w j = m i ^ 2)
    (hdeficit : ∀ i, c * w i ≤ m i ^ 2) :
    ∀ i, (∑ j, (m i ^ 2 * S i j) * w j) ≤ (1 - c) * w i := by
  intro i
  have hs : (∑ j, (m i ^ 2 * S i j) * w j) =
      m i ^ 2 * ∑ j, S i j * w j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  nlinarith [hid i, hdeficit i]

/-- The derivative weight gives an actual inverse bound on the real axis,
including before an inverse has been constructed. -/
theorem real_axis_lower_norm_bound
    (S : Matrix ι ι ℝ) (m w : ι → ℝ) (b B c : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hb : 0 < b) (hB : 0 ≤ B) (hc : 0 < c)
    (hwlo : ∀ i, b ≤ w i) (hwhi : ∀ i, w i ≤ B)
    (hid : ∀ i, w i - m i ^ 2 * ∑ j, S i j * w j = m i ^ 2)
    (hdeficit : ∀ i, c * w i ≤ m i ^ 2) (u : ι → ℂ) :
    ‖u‖ ≤ (B / (b * c)) * ‖stabilityOperator S (fun i => (m i : ℂ)) u‖ := by
  have hw := derivative_weight_contraction S m w c hid hdeficit
  have hh := weighted_lower_norm_bound S (fun i => (m i : ℂ)) w (1 - c) b B
    hS hb hB (by linarith) hwlo hwhi (by simpa using hw) u
  have hone : 1 - (1 - c) = c := by ring
  rw [hone] at hh
  convert hh using 1 <;> ring

/-- Upper operator bound in the finite supremum norm. -/
theorem stability_norm_bound
    (S : Matrix ι ι ℝ) (m u : ι → ℂ) (M R : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hm : ∀ i, ‖m i‖ ≤ M) (hrow : ∀ i, ∑ j, S i j ≤ R) :
    ‖stabilityOperator S m u‖ ≤ (1 + M ^ 2 * R) * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hs : ‖∑ j, (S i j : ℂ) * u j‖ ≤ R * ‖u‖ := by
    calc
      _ ≤ ∑ j, ‖(S i j : ℂ) * u j‖ := norm_sum_le _ _
      _ = ∑ j, S i j * ‖u j‖ := by simp [norm_mul, abs_of_nonneg (hS i _)]
      _ ≤ ∑ j, S i j * ‖u‖ := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (hS i j))
      _ = (∑ j, S i j) * ‖u‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  calc
    ‖stabilityOperator S m u i‖ ≤ ‖u i‖ + ‖m i ^ 2 * ∑ j, (S i j : ℂ) * u j‖ :=
      norm_sub_le _ _
    _ = ‖u i‖ + ‖m i‖ ^ 2 * ‖∑ j, (S i j : ℂ) * u j‖ := by rw [norm_mul, norm_pow]
    _ ≤ ‖u‖ + M ^ 2 * (R * ‖u‖) := add_le_add (norm_le_pi_norm u i)
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hm i) 2) hs
        (norm_nonneg _) (sq_nonneg _))
    _ = _ := by ring

/-- Entrywise continuity of m gives an explicit operator perturbation estimate. -/
theorem stability_difference_bound
    (S : Matrix ι ι ℝ) (m n u : ι → ℂ) (M R δ : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hM : 0 ≤ M) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hm : ∀ i, ‖m i‖ ≤ M) (hn : ∀ i, ‖n i‖ ≤ M)
    (hrow : ∀ i, ∑ j, S i j ≤ R) (hclose : ∀ i, ‖m i - n i‖ ≤ δ) :
    ‖stabilityOperator S m u - stabilityOperator S n u‖ ≤
      (2 * M * R * δ) * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hs : ‖∑ j, (S i j : ℂ) * u j‖ ≤ R * ‖u‖ := by
    calc
      _ ≤ ∑ j, ‖(S i j : ℂ) * u j‖ := norm_sum_le _ _
      _ = ∑ j, S i j * ‖u j‖ := by simp [norm_mul, abs_of_nonneg (hS i _)]
      _ ≤ ∑ j, S i j * ‖u‖ := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (hS i j))
      _ = (∑ j, S i j) * ‖u‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  have heq : stabilityOperator S m u i - stabilityOperator S n u i =
      (n i - m i) * (n i + m i) * ∑ j, (S i j : ℂ) * u j := by
    simp only [stabilityOperator_apply]
    ring
  have hsq : ‖(n i - m i) * (n i + m i)‖ ≤ δ * (2 * M) := by
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul (hclose i) ((norm_add_le _ _).trans (by linarith [hn i, hm i]))
      (norm_nonneg _) hδ
  change ‖stabilityOperator S m u i - stabilityOperator S n u i‖ ≤ _
  rw [heq, norm_mul]
  calc
    _ ≤ (δ * (2 * M)) * (R * ‖u‖) :=
      mul_le_mul hsq hs (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A general lower bound is genuinely an upper bound on the norm of the
inverse continuous linear operator. -/
theorem inverse_norm_of_lower_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u, ‖u‖ ≤ C * ‖stabilityOperator S m u‖) :
    ‖(stabilityContinuousEquiv hS hz hm hsol).symm.toContinuousLinearMap‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hh := hbound ((stabilityContinuousEquiv hS hz hm hsol).symm v)
  have hid : stabilityOperator S m ((stabilityContinuousEquiv hS hz hm hsol).symm v) = v :=
    (stabilityContinuousEquiv hS hz hm hsol).apply_symm_apply v
  simpa only [hid] using hh

theorem inverse_norm_lower_bound [Nonempty ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (M R : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hmod : ∀ i, ‖m i‖ ≤ M) (hrow : ∀ i, ∑ j, S i j ≤ R) :
    1 / (1 + M ^ 2 * R) ≤
      ‖(stabilityContinuousEquiv hS hz hm hsol).symm.toContinuousLinearMap‖ := by
  let e := stabilityContinuousEquiv hS hz hm hsol
  have he : ‖e.toContinuousLinearMap‖ ≤ 1 + M ^ 2 * R := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    exact stability_norm_bound S m u M R hS hM hR hmod hrow
  have hh := e.one_le_norm_mul_norm_symm
  have hmul := mul_le_mul_of_nonneg_right he (norm_nonneg e.symm.toContinuousLinearMap)
  apply (div_le_iff₀ (by positivity : 0 < 1 + M ^ 2 * R)).mpr
  change 1 ≤ ‖e.symm.toContinuousLinearMap‖ * (1 + M ^ 2 * R)
  nlinarith

/-- A complex perturbation of perpendicular nonnegative real/imaginary
leading terms cannot cancel their total size when the remainder is small. -/
theorem perpendicular_absorption
    (A B ε : ℝ) (e β : ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (he : ‖e‖ ≤ ε * (A + B))
    (hβ : β = (A : ℂ) + (B : ℂ) * Complex.I + e) :
    (1 / 2 - ε) * (A + B) ≤ ‖β‖ := by
  let v : ℂ := (A : ℂ) + (B : ℂ) * Complex.I
  have hra : A ≤ ‖v‖ := by
    simpa [v, abs_of_nonneg hA] using Complex.abs_re_le_norm v
  have hia : B ≤ ‖v‖ := by
    simpa [v, abs_of_nonneg hB] using Complex.abs_im_le_norm v
  have ht : ‖v‖ ≤ ‖β‖ + ‖e‖ := by
    have hv : v = β - e := by rw [hβ]; dsimp [v]; ring
    rw [hv]
    exact norm_sub_le _ _
  nlinarith

/-- Positive real leading terms give the cusp lower bound even in the
presence of an arbitrary imaginary coefficient. -/
theorem positive_real_absorption
    (A B C ε : ℝ) (e β : ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : ‖e‖ ≤ ε * (A + B))
    (hβ : β = ((A + B : ℝ) : ℂ) + (C : ℂ) * Complex.I + e) :
    (1 - ε) * (A + B) ≤ ‖β‖ := by
  have hreal : A + B = β.re - e.re := by
    rw [hβ]
    simp
  have hbr : β.re ≤ ‖β‖ := (le_abs_self _).trans (Complex.abs_re_le_norm β)
  have her : -e.re ≤ ‖e‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm e)
  nlinarith

end NonSymmetricDyson.Full.Linear
