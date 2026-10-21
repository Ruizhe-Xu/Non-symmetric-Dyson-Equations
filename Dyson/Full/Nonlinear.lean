import Mathlib
import Dyson.Model
import Dyson.WeightedMaximum
import Dyson.Full.NonlinearRoots
import Dyson.Full.NonlinearAnalytic
import Dyson.Full.NonlinearReduction
import Dyson.Full.NonlinearRough

/-!
Nonlinear estimates for the actual finite-dimensional Dyson residual.
This module does not axiomatize any nonlinear stability conclusion.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Nonlinear

open BasicEstimates

variable {ι : Type*} [Fintype ι]

theorem exact_product_identity
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (hm : IsDysonSolution S a z m) (hm0 : ∀ i, m i ≠ 0)
    (hg0 : ∀ i, g i ≠ 0) (i : ι) :
    g i - m i = m i * g i *
      (Model.action S (g - m) i + Model.residual S a z g i) := by
  have h := DysonPaper.Algebra.scalar_dyson_product
    (m i) (g i) (z - (a i : ℂ)) (Model.action S m i)
    (Model.action S g i) (Model.residual S a z g i)
    (hm0 i) (hg0 i) (hm i)
    (by simp only [Model.residual]; ring)
  simpa only [map_sub, Pi.sub_apply] using h

theorem residual_equation
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (g : ι → ℂ) (i : ι) :
    -(g i)⁻¹ = z - (a i : ℂ) +
      ∑ j, (S i j : ℂ) * g j + Model.residual S a z g i := by
  simp only [Model.residual, Model.action_apply]
  ring

theorem action_norm_le
    (S : Matrix ι ι ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (u : ι → ℂ) (i : ι) :
    ‖Model.action S u i‖ ≤ ∑ j, S i j * ‖u j‖ := by
  change ‖∑ j, (S i j : ℂ) * u j‖ ≤ _
  calc
    _ ≤ ∑ j, ‖(S i j : ℂ) * u j‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hS i j)]

/-- A uniform row-sum bound controls the actual matrix action. -/
theorem action_norm_le_uniform
    (S : Matrix ι ι ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (s U : ℝ) (hU : 0 ≤ U) (hrow : ∀ i, ∑ j, S i j ≤ s)
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ ≤ U) (i : ι) :
    ‖Model.action S u i‖ ≤ s * U := by
  calc
    _ ≤ ∑ j, S i j * ‖u j‖ := action_norm_le S hS u i
    _ ≤ ∑ j, S i j * U := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hu j) (hS i j)
    _ = (∑ j, S i j) * U := (Finset.sum_mul _ _ _).symm
    _ ≤ s * U := mul_le_mul_of_nonneg_right (hrow i) hU

/-- The perturbed equation supplies the missing large-height denominator bound.
Unlike a lower bound for |g|, this statement remains valid as Im z tends to infinity. -/
theorem large_height_g_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hS : ∀ i j, 0 ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ s)
    (hm : IsUpperSolution m) (hg0 : ∀ i, g i ≠ 0)
    (hclose : ∀ i, ‖g i - m i‖ ≤ c)
    (hres : ∀ i, ‖Model.residual S a z g i‖ ≤ c)
    (hheight : 2 * (s + 1) ≤ z.im) (i : ι) :
    ‖g i‖ ≤ 2 / z.im := by
  have hz : 0 < z.im := by linarith
  have him : ∀ j, -c ≤ (g j).im := by
    intro j
    have h := Complex.abs_im_le_norm (g j - m j)
    have h' := neg_le_abs (g j - m j).im
    have hp := hm j
    simp only [Complex.sub_im] at h h'
    linarith [hclose j]
  have hR : -c ≤ (Model.residual S a z g i).im := by
    have h := Complex.abs_im_le_norm (Model.residual S a z g i)
    have h' := neg_le_abs (Model.residual S a z g i).im
    linarith [hres i]
  have hsum : -s * c ≤ ∑ j, S i j * (g j).im := by
    calc
      -s * c = s * (-c) := by ring
      _ ≤ (∑ j, S i j) * (-c) :=
        mul_le_mul_of_nonpos_right (hrow i) (neg_nonpos.mpr hc)
      _ = ∑ j, S i j * (-c) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (him j) (hS i j)
  have hEq := congrArg Complex.im (residual_equation S a z g i)
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    sub_zero, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    zero_mul, add_zero] at hEq
  have himinv : z.im / 2 ≤ (-(g i)⁻¹).im := by
    have hsc : s * c ≤ s := by nlinarith
    linarith
  have hnorminv : z.im / 2 ≤ ‖g i‖⁻¹ := by
    calc
      _ ≤ (-(g i)⁻¹).im := himinv
      _ ≤ ‖-(g i)⁻¹‖ := Complex.im_le_norm _
      _ = ‖g i‖⁻¹ := by simp
  have hnormpos : 0 < ‖g i‖ := norm_pos_iff.mpr (hg0 i)
  have hbound : ‖g i‖ ≤ (z.im / 2)⁻¹ :=
    (le_inv_comm₀ (by positivity : 0 < z.im / 2) hnormpos).mp hnorminv
  simpa only [inv_div, one_div] using hbound

/-- Quantified repair of the large-height nonlinear stability estimate.
The residual bound E is arbitrary and need not equal the closeness parameter c. -/
theorem large_height_stability
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (s c E : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hE : 0 ≤ E) (hS : ∀ i j, 0 ≤ S i j)
    (hrow : ∀ i, ∑ j, S i j ≤ s)
    (hm : IsUpperSolution m) (hsol : IsDysonSolution S a z m)
    (hg0 : ∀ i, g i ≠ 0)
    (hclose : ∀ i, ‖g i - m i‖ ≤ c)
    (hres : ∀ i, ‖Model.residual S a z g i‖ ≤ c)
    (hresE : ∀ i, ‖Model.residual S a z g i‖ ≤ E)
    (hheight : 2 * (s + 1) ≤ z.im) (i : ι) :
    ‖g i - m i‖ ≤ 4 / z.im ^ 2 * E := by
  have hz : 0 < z.im := by linarith
  have hz2 : 0 < z.im ^ 2 := sq_pos_of_pos hz
  have hg := large_height_g_bound S a z m g s c hs hc hc1 hS hrow
    hm hg0 hclose hres hheight
  have hm0 := component_ne_zero hm
  have hrough := rough_bound hS hz hm hsol
  have hprod : ∀ j, ‖m j‖ * ‖g j‖ ≤ 2 / z.im ^ 2 := by
    intro j
    calc
      _ ≤ z.im⁻¹ * (2 / z.im) :=
        mul_le_mul (hrough j) (hg j) (norm_nonneg _) (inv_nonneg.mpr hz.le)
      _ = _ := by field_simp
  have hscalar : ∀ j, ‖g j - m j‖ ≤
      ∑ k, (2 / z.im ^ 2 * S j k) * ‖g k - m k‖ + 2 / z.im ^ 2 * E := by
    intro j
    rw [exact_product_identity S a z m g hsol hm0 hg0 j, norm_mul, norm_mul]
    calc
      _ ≤ (2 / z.im ^ 2) *
          (‖Model.action S (g - m) j‖ + ‖Model.residual S a z g j‖) :=
        mul_le_mul (hprod j) (norm_add_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ (2 / z.im ^ 2) * ((∑ k, S j k * ‖g k - m k‖) + E) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (action_norm_le S hS (g - m) j) (hresE j)
      _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hheight2 : 4 * s ≤ z.im ^ 2 := by nlinarith [sq_nonneg s]
  have hcontract : ∀ j, ∑ k, (2 / z.im ^ 2 * S j k) * (1 : ℝ) ≤
      (1 / 2 : ℝ) * 1 := by
    intro j
    simp only [mul_one, ← Finset.mul_sum]
    apply le_trans (mul_le_mul_of_nonneg_left (hrow j) (by positivity))
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hz2).mpr
    nlinarith
  have h := UniquenessAux.bound_of_weighted_contraction
    (fun j k => 2 / z.im ^ 2 * S j k) (fun _ => (1 : ℝ))
    (fun j => ‖g j - m j‖) (fun _ => 2 / z.im ^ 2 * E)
    (1 / 2) (2 / z.im ^ 2 * E)
    (fun j k => mul_nonneg (by positivity) (hS j k))
    (fun _ => zero_lt_one) (fun _ => norm_nonneg _) (by norm_num)
    hscalar hcontract (by intro j; simp) i
  convert h using 1 <;> ring

/-- Scalar absorption with its exact smallness condition, used only after an
actual displacement inequality has been obtained. -/
theorem quadratic_absorption {U B A : ℝ}
    (hU : 0 ≤ U) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hsmall : A * U ≤ 1 / 2) (hineq : U ≤ B + A * U ^ 2) :
    U ≤ 2 * B := by
  have h := mul_le_mul_of_nonneg_right hsmall hU
  nlinarith

/-- Reverse triangle inequality in the precise form needed before dividing by g. -/
theorem close_coordinates_nonzero (m g : ℂ) (b : ℝ)
    (hb : 0 < b) (hm : b ≤ ‖m‖) (hclose : ‖g - m‖ ≤ b / 2) :
    b / 2 ≤ ‖g‖ ∧ g ≠ 0 := by
  have ht : ‖m‖ ≤ ‖g‖ + ‖g - m‖ := by
    calc
      ‖m‖ = ‖g - (g - m)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hlow : b / 2 ≤ ‖g‖ := by linarith
  exact ⟨hlow, norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hlow)⟩

/-- Exact scalar vertex reconstruction and its quadratic error. -/
theorem vertex_reconstruction_expansion (d δ : ℂ) (hd : d ≠ 0)
    (hg : d + δ ≠ 0) :
    -(d + δ)⁻¹ - (-d⁻¹) =
      (-d⁻¹)^2 * δ + (-d⁻¹)^3 * δ^2 / (1 - (-d⁻¹) * δ) := by
  have hden : 1 - (-d⁻¹) * δ ≠ 0 := by
    intro h
    apply hg
    field_simp at h
    linear_combination h
  field_simp [hd, hg, hden]
  ring

/-- The basic denominator estimate controlling vertex reconstruction. -/
theorem one_sub_product_lower (v δ : ℂ) (h : ‖v * δ‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖1 - v * δ‖ ∧ 1 - v * δ ≠ 0 := by
  have ht := norm_sub_norm_le (1 : ℂ) (v * δ)
  have hlow : (1 / 2 : ℝ) ≤ ‖1 - v * δ‖ := by
    simp only [norm_one] at ht
    linarith
  exact ⟨hlow, norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hlow)⟩

/-- The actual inverse/coercivity estimate is the only linear input here.
All reciprocal and quadratic estimates are proved for the computed residual. -/
theorem bounded_height_stability
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (b M A : ℝ) (hb : 0 < b) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hm0 : ∀ i, m i ≠ 0) (hsol : IsDysonSolution S a z m)
    (hlo : ∀ i, b ≤ ‖m i‖) (hhi : ∀ i, ‖m i‖ ≤ M)
    (hclose : ‖g - m‖ ≤ b / 2)
    (hsmall : 4 * A * ‖g - m‖ ≤ b)
    (hlinear : ∀ u : ι → ℂ, ‖u‖ ≤ A *
      ‖DysonPaper.Algebra.stabilityAction m (Model.action S) u‖) :
    ‖g - m‖ ≤ 2 * A * M ^ 2 * ‖Model.residual S a z g‖ := by
  have hg : ∀ i, b / 2 ≤ ‖g i‖ ∧ g i ≠ 0 := by
    intro i
    apply close_coordinates_nonzero (m i) (g i) b hb (hlo i)
    exact (norm_le_pi_norm (g - m) i).trans hclose
  have hvec :
      ‖DysonPaper.Algebra.stabilityAction m (Model.action S) (g - m)‖ ≤
        M ^ 2 * ‖Model.residual S a z g‖ + (2 / b) * ‖g - m‖ ^ 2 := by
    rw [Model.exact_residual_expansion S a z m g hsol hm0 (fun i => (hg i).2)]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hsq : ‖m i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (m i), hhi i]
    have hsqU : ‖g i - m i‖ ^ 2 ≤ ‖g - m‖ ^ 2 := by
      have ht := norm_le_pi_norm (g - m) i
      simp only [Pi.sub_apply] at ht
      nlinarith [norm_nonneg (g i - m i)]
    have hquot : ‖g i - m i‖ ^ 2 / ‖g i‖ ≤ (2 / b) * ‖g - m‖ ^ 2 := by
      have hgpos : 0 < ‖g i‖ := norm_pos_iff.mpr (hg i).2
      apply (div_le_iff₀ hgpos).mpr
      have hmul : ‖g - m‖ ^ 2 ≤ ((2 / b) * ‖g - m‖ ^ 2) * ‖g i‖ := by
        have hden : (1 : ℝ) ≤ (2 / b) * ‖g i‖ := by
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hb).mpr
          nlinarith [(hg i).1]
        nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg ‖g - m‖)]
      exact hsqU.trans hmul
    calc
      _ ≤ ‖m i ^ 2 * Model.residual S a z g i‖ + ‖(g i - m i) ^ 2 / g i‖ :=
        norm_add_le _ _
      _ = ‖m i‖ ^ 2 * ‖Model.residual S a z g i‖ + ‖g i - m i‖ ^ 2 / ‖g i‖ := by
        simp only [norm_mul, norm_pow, norm_div]
      _ ≤ _ := add_le_add
        (mul_le_mul hsq (norm_le_pi_norm (Model.residual S a z g) i)
          (norm_nonneg _) (sq_nonneg M)) hquot
  have hineq : ‖g - m‖ ≤ A * M ^ 2 * ‖Model.residual S a z g‖ +
      (2 * A / b) * ‖g - m‖ ^ 2 := by
    have h := (hlinear (g - m)).trans (mul_le_mul_of_nonneg_left hvec hA)
    convert h using 1 <;> ring
  have habs : (2 * A / b) * ‖g - m‖ ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hb).mpr
    nlinarith
  have h := quadratic_absorption (norm_nonneg (g - m))
    (show 0 ≤ A * M ^ 2 * ‖Model.residual S a z g‖ by positivity)
    (show 0 ≤ 2 * A / b by positivity) habs hineq
  convert h using 1 <;> ring

/-- The reciprocal vertex formula is defined whenever the relative increment
has modulus at most one half. -/
theorem vertex_denominator_nonzero (d δ : ℂ) (hd : d ≠ 0)
    (hsmall : ‖(-d⁻¹) * δ‖ ≤ 1 / 2) : d + δ ≠ 0 := by
  have h := (one_sub_product_lower (-d⁻¹) δ hsmall).2
  intro heq
  apply h
  have hδ : δ = -d := by linear_combination heq
  rw [hδ]
  field_simp [hd]
  ring

theorem vertex_quadratic_remainder (d δ : ℂ) (hd : d ≠ 0)
    (hsmall : ‖(-d⁻¹) * δ‖ ≤ 1 / 2) :
    ‖-(d + δ)⁻¹ - (-d⁻¹) - (-d⁻¹)^2 * δ‖ ≤
      2 * ‖-d⁻¹‖ ^ 3 * ‖δ‖ ^ 2 := by
  have hg := vertex_denominator_nonzero d δ hd hsmall
  have hden := one_sub_product_lower (-d⁻¹) δ hsmall
  rw [vertex_reconstruction_expansion d δ hd hg]
  rw [add_sub_cancel_left, norm_div, norm_mul, norm_pow, norm_pow]
  apply (div_le_iff₀ (norm_pos_iff.mpr hden.2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden.1
    (show 0 ≤ ‖-d⁻¹‖ ^ 3 * ‖δ‖ ^ 2 by positivity)]

/-- The bipartite direction is evaluated using the actual Dyson equation and
the signed anticommutation identity. -/
theorem bipartite_direction_identity
    (S : Matrix ι ι ℝ) (z : ℂ) (m T : ι → ℂ)
    (hm : IsDysonSolution S (fun _ => 0) z m) (hm0 : ∀ i, m i ≠ 0)
    (hanti : Model.action S (T * m) = -T * Model.action S m) :
    DysonPaper.Algebra.stabilityAction m (Model.action S) (T * m) =
      fun i => -z * T i * m i ^ 2 := by
  ext i
  have he := hm i
  simp only [Complex.ofReal_zero, sub_zero] at he
  have ha := congrFun hanti i
  change T i * m i - m i ^ 2 * Model.action S (T * m) i = _
  simp only [Pi.mul_apply, Pi.neg_apply] at ha
  rw [ha]
  change -(m i)⁻¹ = z + Model.action S m i at he
  have hinv : m i * (m i)⁻¹ = 1 := mul_inv_cancel₀ (hm0 i)
  linear_combination -(m i ^ 2 * T i) * he - T i * m i * hinv

/-- An injective restriction stays quantitatively injective under a small
operator perturbation. This is the fixed-complement estimate used at zero. -/
theorem complement_perturbation_bound
    (A₀ A : (ι → ℂ) →L[ℂ] (ι → ℂ)) (X : Submodule ℂ (ι → ℂ))
    (c : ℝ) (hc : 0 < c)
    (hbase : ∀ w ∈ X, c * ‖w‖ ≤ ‖A₀ w‖)
    (hperturb : ‖A - A₀‖ ≤ c / 2)
    (w : ι → ℂ) (hw : w ∈ X) :
    ‖w‖ ≤ (2 / c) * ‖A w‖ := by
  have hdiff : ‖(A - A₀) w‖ ≤ c / 2 * ‖w‖ :=
    ((A - A₀).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hperturb (norm_nonneg _))
  have ht : ‖A₀ w‖ ≤ ‖A w‖ + ‖(A - A₀) w‖ := by
    calc
      _ = ‖A w - (A - A₀) w‖ := by congr 1; simp
      _ ≤ _ := norm_sub_le _ _
  have h := hbase w hw
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- The fixed-complement decomposition is explicit once a nonvanishing
linear coordinate on the moving direction is chosen. -/
theorem fixed_complement_decomposition
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (b u : ι → ℂ) (hb : ℓ b ≠ 0) :
    let θ := ℓ u / ℓ b
    let w := u - θ • b
    u = θ • b + w ∧ ℓ w = 0 := by
  dsimp
  constructor
  · abel
  · simp only [map_sub, map_smul, smul_eq_mul]
    field_simp [hb]
    ring

/-- The coefficient controlling the vertex balance does not vanish at a
regular bulk point because its imaginary part is strictly positive. -/
theorem vertex_balance_coefficient_ne_zero
    {κ : Type*} [Fintype κ] [Nonempty κ] (v : κ → ℂ)
    (hv : ∀ i, 0 < (v i).im) : (∑ i, v i) ≠ 0 := by
  have hpos : 0 < (∑ i, v i).im := by
    rw [Complex.im_sum]
    exact Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  intro h
  simp [h] at hpos

/-- Algebra behind the bipartite coefficient `Σ(v + z*v²)`. -/
theorem vertex_balance_coefficient_identity
    {κ : Type*} [Fintype κ] (v neighborSum : κ → ℂ) (z : ℂ)
    (hv : ∀ i, v i ≠ 0)
    (heq : ∀ i, neighborSum i = -(v i)⁻¹ - z) :
    -(∑ i, v i ^ 2 * neighborSum i) = ∑ i, (v i + z * v i ^ 2) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [heq i]
  field_simp [hv i]
  ring

/-- Large-height reconstructed vertex denominators are controlled directly
by their imaginary parts, without any coordinatewise lower bound on `g`. -/
theorem large_height_vertex_denominator_bound
    {κ : Type*} (B : κ → ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (D c : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hB : ∀ i j, 0 ≤ B i j) (hrow : ∀ i, ∑ j, B i j ≤ D)
    (hm : IsUpperSolution m) (hclose : ∀ j, ‖g j - m j‖ ≤ c)
    (hz : 0 < z.im) (hheight : 2 * D ≤ z.im) (i : κ) :
    z + (∑ j, (B i j : ℂ) * g j) ≠ 0 ∧
      ‖-(z + (∑ j, (B i j : ℂ) * g j))⁻¹‖ ≤ 2 / z.im := by
  have him : ∀ j, -c ≤ (g j).im := by
    intro j
    have h₁ := Complex.abs_im_le_norm (g j - m j)
    have h₂ := neg_le_abs (g j - m j).im
    have h₃ := hm j
    simp only [Complex.sub_im] at h₁ h₂
    linarith [hclose j]
  have hsum : -D * c ≤ ∑ j, B i j * (g j).im := by
    calc
      _ = D * (-c) := by ring
      _ ≤ (∑ j, B i j) * (-c) :=
        mul_le_mul_of_nonpos_right (hrow i) (neg_nonpos.mpr hc)
      _ = ∑ j, B i j * (-c) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (him j) (hB i j)
  have hden : z.im / 2 ≤ (z + ∑ j, (B i j : ℂ) * g j).im := by
    simp only [Complex.add_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    nlinarith
  have hnorm : z.im / 2 ≤ ‖z + ∑ j, (B i j : ℂ) * g j‖ := hden.trans (Complex.im_le_norm _)
  have hnormpos : 0 < ‖z + ∑ j, (B i j : ℂ) * g j‖ := lt_of_lt_of_le (by positivity) hnorm
  refine ⟨norm_pos_iff.mp hnormpos, ?_⟩
  rw [norm_neg, norm_inv]
  have hbound : ‖z + ∑ j, (B i j : ℂ) * g j‖⁻¹ ≤ (z.im / 2)⁻¹ :=
    inv_anti₀ (by positivity : 0 < z.im / 2) hnorm
  simpa only [inv_div, one_div] using hbound

end NonSymmetricDyson.Full.Nonlinear
