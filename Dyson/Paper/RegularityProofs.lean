import Dyson.Paper.Foundations
import Dyson.Full.Poisson
import Mathlib.Analysis.Calculus.MeanValue

/-! Literal differentiation-under-the-integral and convex-segment proof in
revised M4, lines 1620--1663. All measure integrals are actual Bochner integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.RegularityProofs
open Full.Poisson

private theorem height_denominator {z : ℂ} (hz : 0 ≤ z.im) (t : ℝ) :
    z.im ≤ ‖(t:ℂ)-z‖ := by
  have h := height_le_norm z.re t hz
  simpa [point] using h

/-- Differentiation of the Stieltjes integral at any point of the open upper
half-plane, using the positive half-height disk as a common dominating set. -/
theorem stieltjes_hasDerivAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (stieltjes μ) (∫ t, Full.Poisson.resolvent z t ^ 2 ∂μ) z := by
  have hh : 0 < z.im/2 := by positivity
  have hn : ∀ (t : ℝ) (w : ℂ), w ∈ Metric.ball z (z.im/2) →
      z.im/2 ≤ ‖(t:ℂ)-w‖ := by
    intro t w hw
    have hd : ‖w-z‖ < z.im/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hi : |w.im-z.im| ≤ ‖w-z‖ := by simpa using Complex.abs_im_le_norm (w-z)
    have hwi : z.im/2 ≤ w.im := by linarith [neg_abs_le (w.im-z.im)]
    exact hwi.trans (height_denominator (hh.le.trans hwi) t)
  have hder : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball z (z.im/2),
      HasDerivAt (fun v => Full.Poisson.resolvent v t) (Full.Poisson.resolvent w t ^ 2) w := by
    filter_upwards [] with t
    intro w hw
    exact hasDerivAt_resolvent (norm_pos_iff.mp (hh.trans_le (hn t w hw)))
  have hb : ∀ᵐ (t : ℝ) ∂μ, ∀ w ∈ Metric.ball z (z.im/2),
      ‖Full.Poisson.resolvent w t ^ 2‖ ≤ ((z.im/2)⁻¹)^2 := by
    filter_upwards [] with t
    intro w hw
    have hi : ‖Full.Poisson.resolvent w t‖ ≤ (z.im/2)⁻¹ := by
      simpa [Full.Poisson.resolvent] using
        (inv_le_inv₀ (hh.trans_le (hn t w hw)) hh).mpr (hn t w hw)
    simpa [norm_pow, pow_two] using mul_self_le_mul_self (norm_nonneg _) hi
  have hint : Integrable (Full.Poisson.resolvent z) μ := by
    simpa [point] using resolvent_integrable_of_height μ z.re hz
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun z t => Full.Poisson.resolvent z t) (F' := fun z t => Full.Poisson.resolvent z t ^ 2)
    (bound := fun _ => ((z.im/2)⁻¹)^2) hh
    (Eventually.of_forall fun w => (measurable_resolvent w).aestronglyMeasurable)
    hint ((measurable_resolvent z).pow_const 2).aestronglyMeasurable
    hb (integrable_const _) hder).2

/-- The source bound includes the actual total mass μ(ℝ); probability is a
special case. -/
theorem stieltjes_derivative_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (η₀ : ℝ) (hη₀ : 0 < η₀) (z : ℂ) (hz : η₀ ≤ z.im) :
    ‖∫ t, Full.Poisson.resolvent z t ^ 2 ∂μ‖ ≤ μ.real univ * (η₀⁻¹)^2 := by
  have hh : 0 < z.im := hη₀.trans_le hz
  have hres (t : ℝ) : ‖Full.Poisson.resolvent z t‖ ≤ η₀⁻¹ := by
    have hi : ‖Full.Poisson.resolvent z t‖ ≤ z.im⁻¹ := by
      simpa [point] using resolvent_norm_of_height z.re t hh
    exact hi.trans ((inv_le_inv₀ hh hη₀).mpr hz)
  have hb : ∀ᵐ t ∂μ, ‖Full.Poisson.resolvent z t ^ 2‖ ≤ (η₀⁻¹)^2 :=
    Eventually.of_forall fun t => by
      simpa [norm_pow, pow_two] using mul_self_le_mul_self (norm_nonneg _) (hres t)
  simpa only [mul_comm] using norm_integral_le_of_norm_le_const hb

/-- The line segment remains above η₀, so the derivative estimate gives the
literal mean-value Lipschitz estimate used in the manuscript. -/
theorem stieltjes_lipschitz_above_height (μ : Measure ℝ) [IsFiniteMeasure μ]
    (η₀ : ℝ) (hη₀ : 0 < η₀) (z w : ℂ) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) :
    ‖stieltjes μ z - stieltjes μ w‖ ≤
      (μ.real univ * (η₀⁻¹)^2) * ‖z-w‖ := by
  let U : Set ℂ := {v | η₀ ≤ v.im}
  have hc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change η₀ ≤ (a • x + b • y).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have hax := mul_le_mul_of_nonneg_left hx ha
    have hby := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (stieltjes_hasDerivAt μ v (hη₀.trans_le hv)).hasDerivWithinAt)
    (fun v hv => stieltjes_derivative_bound μ η₀ hη₀ v hv) hc hw hz

/-- Actual canonical M1 measures instantiate the derivative formula; neither
an auxiliary function nor an unproved Dyson-specific derivative is assumed. -/
theorem solution_hasDerivAt {n : ℕ} (hn : 0 < n)
    (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (i : Fin n) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (fun w => Foundations.solution S a hS w i)
      (∫ t, (((t:ℂ)-z)⁻¹)^2 ∂Foundations.measure S a hn external hS i) z := by
  let μ := Foundations.measure S a hn external hS i
  letI : IsProbabilityMeasure μ := (Foundations.measure_spec S a hn external hS i).1
  have hrep := (Foundations.measure_spec S a hn external hS i).2.1
  apply (stieltjes_hasDerivAt μ z hz).congr_of_eventuallyEq
  filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz] with w hw
  exact hrep w hw

end NonSymmetricDyson.Paper.RegularityProofs
