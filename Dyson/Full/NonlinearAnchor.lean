import Dyson.Full.Nonlinear
import Dyson.Full.Linear

/-! The fixed positive height anchor is derived from the actual Dyson equation.
It is not an extra branch-selection hypothesis. -/

noncomputable section
namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

/-- Uniform nonlinear stability on a closed middle-height rectangle, with
one closeness radius for all actual solutions in that rectangle. -/
theorem middle_rectangle_nonlinear_stability
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (T h H : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hT : 0 ≤ T) (hh : 0 < h) (hH : h ≤ H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (m g : ι → ℂ),
      |z.re| ≤ T → h ≤ z.im → z.im ≤ H →
      BasicEstimates.IsUpperSolution m → BasicEstimates.IsDysonSolution S a z m →
      ‖g - m‖ ≤ c → ‖g - m‖ ≤ C * ‖Model.residual S a z g‖ := by
  let b := ComponentBounds.uniformLowerConstant S a h⁻¹ / (1 + T + H)
  have hbase := ComponentBounds.uniformLowerConstant_pos (a := a) hS (inv_pos.mpr hh).le
  have hden : 0 < 1 + T + H := by linarith
  have hb : 0 < b := div_pos hbase hden
  obtain ⟨A, hA, hlinear⟩ := Linear.middle_rectangle_lower_norm_bound S a T h H hS hT hh hH
  let c := min (b / 2) (b / (4 * A))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, 2 * A * (h⁻¹) ^ 2, hc, by positivity, ?_⟩
  intro z m g hreal hheight hhigh hm hsol hclose
  have hz : 0 < z.im := hh.trans_le hheight
  have hupper : ∀ i, ‖m i‖ ≤ h⁻¹ := fun i =>
    (BasicEstimates.rough_bound hS hz hm hsol i).trans (inv_anti₀ hh hheight)
  have hzn : ‖z‖ ≤ T + H := by
    have ht := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at ht
    linarith
  have hlower : ∀ i, b ≤ ‖m i‖ := by
    intro i
    calc
      b ≤ ComponentBounds.uniformLowerConstant S a h⁻¹ / (1 + ‖z‖) :=
        div_le_div_of_nonneg_left hbase.le (by positivity) (by linarith)
      _ ≤ ‖m i‖ := ComponentBounds.common_scaled_lower_bound hS hm hsol
        (inv_pos.mpr hh).le hupper i
  have hcloseb : ‖g - m‖ ≤ b / 2 := hclose.trans (min_le_left _ _)
  have hsmall : 4 * A * ‖g - m‖ ≤ b := by
    have hbound : ‖g - m‖ ≤ b / (4 * A) := hclose.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 4 * A)).mp hbound
    nlinarith
  exact bounded_height_stability S a z m g b (h⁻¹) A hb (inv_nonneg.mpr hh.le) hA.le
    (BasicEstimates.component_ne_zero hm) hsol hlower hupper hcloseb hsmall
    (hlinear z m hreal hheight hhigh hm hsol)

/-- The vertical proof path has a quantitative anchor at its fixed top height. -/
theorem fixed_height_nonlinear_anchor
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ r H : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hr : 0 ≤ r) (hH : 0 < H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (m g : ι → ℂ),
      |z.re - τ| ≤ r → z.im = H →
      BasicEstimates.IsUpperSolution m → BasicEstimates.IsDysonSolution S a z m →
      ‖g - m‖ ≤ c → ‖g - m‖ ≤ C * ‖Model.residual S a z g‖ := by
  obtain ⟨c, C, hc, hC, hbound⟩ := middle_rectangle_nonlinear_stability S a
    (|τ| + r) H H hS (by positivity) hH le_rfl
  refine ⟨c, C, hc, hC, ?_⟩
  intro z m g hreal him hm hsol hclose
  apply hbound z m g ?_ (by rw [him]) (by rw [him]) hm hsol hclose
  have htri : |z.re| ≤ |z.re - τ| + |τ| := by
    simpa only [sub_add_cancel] using abs_add_le (z.re - τ) τ
  linarith

/-- Normalization converts the vector anchor into the actual Lyapunov--Schmidt
scalar anchor. No coordinatewise lower bound needs to be introduced here. -/
theorem normalized_scalar_displacement_bound
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (q mτ g m : ι → ℂ) :
    ‖ℓ ((g - mτ) / q) - ℓ ((m - mτ) / q)‖ ≤
      (‖ℓ‖ * ‖q⁻¹‖) * ‖g - m‖ := by
  have he : (g - mτ) / q - (m - mτ) / q = (g - m) * q⁻¹ := by
    ext i
    simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    ring
  rw [← map_sub, he]
  calc
    _ ≤ ‖ℓ‖ * ‖(g - m) * q⁻¹‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (‖g - m‖ * ‖q⁻¹‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The scalar anchor with a uniform residual majorant. -/
theorem fixed_height_scalar_anchor
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ r H : ℝ)
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (q mτ : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hr : 0 ≤ r) (hH : 0 < H) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (m g : ι → ℂ) (E : ℝ),
      |z.re - τ| ≤ r → z.im = H →
      BasicEstimates.IsUpperSolution m → BasicEstimates.IsDysonSolution S a z m →
      ‖g - m‖ ≤ c → ‖Model.residual S a z g‖ ≤ E →
      ‖ℓ ((g - mτ) / q) - ℓ ((m - mτ) / q)‖ ≤ C * E := by
  obtain ⟨c, C, hc, hC, hbound⟩ := fixed_height_nonlinear_anchor S a τ r H hS hr hH
  refine ⟨c, 1 + (‖ℓ‖ * ‖q⁻¹‖) * C, hc, by positivity, ?_⟩
  intro z m g E hreal him hm hsol hclose hres
  have hE : 0 ≤ E := (norm_nonneg _).trans hres
  calc
    _ ≤ (‖ℓ‖ * ‖q⁻¹‖) * ‖g - m‖ := normalized_scalar_displacement_bound ℓ q mτ g m
    _ ≤ (‖ℓ‖ * ‖q⁻¹‖) * (C * ‖Model.residual S a z g‖) :=
      mul_le_mul_of_nonneg_left (hbound z m g hreal him hm hsol hclose) (by positivity)
    _ ≤ (‖ℓ‖ * ‖q⁻¹‖) * (C * E) := by gcongr
    _ ≤ (1 + (‖ℓ‖ * ‖q⁻¹‖) * C) * E := by nlinarith

end NonSymmetricDyson.Full.Nonlinear
