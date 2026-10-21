import Dyson.Full.SingularitiesReflection
import Dyson.Full.Linear

/-! Exact differential identities for the actual singular Dyson solution
curve. These connect the constructed analytic graph with the stability
operator without assuming a Dyson-specific spectral conclusion. -/

noncomputable section
open scoped Topology BigOperators
open Filter

namespace NonSymmetricDyson.Full.SingularLinear

variable {ι : Type*} [Fintype ι]

/-- Differentiate the actual denominator-free Dyson equation along any
complex differentiable solution curve. -/
theorem dyson_curve_derivative
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ → ℂ) (m : ℂ → ι → ℂ)
    (θ z' : ℂ) (u : ι → ℂ)
    (hz : HasDerivAt z z' θ) (hm : HasDerivAt m u θ)
    (hsol : ∀ᶠ t in 𝓝 θ, PolynomialDyson.IsPolynomialSolution S a (z t) (m t)) :
    InteriorStability.stabilityOperator S (m θ) u =
      fun i => z' * (m θ i) ^ 2 := by
  have hbase : PolynomialDyson.IsPolynomialSolution S a (z θ) (m θ) :=
    mem_of_mem_nhds hsol
  funext i
  have hmcoord := hasDerivAt_pi.mp hm
  have hsum : HasDerivAt (fun t => ∑ j, (S i j : ℂ) * m t j)
      (∑ j, (S i j : ℂ) * u j) θ := by
    exact HasDerivAt.fun_sum (fun j _ => (hmcoord j).const_mul (S i j : ℂ))
  have hproduct := (hmcoord i).mul ((hz.sub_const (a i : ℂ)).add hsum)
  have hconst : HasDerivAt (fun _ : ℂ => (-1 : ℂ))
      (u i * (z θ - (a i : ℂ) + ∑ j, (S i j : ℂ) * m θ j) +
        m θ i * (z' + ∑ j, (S i j : ℂ) * u j)) θ := by
    apply hproduct.congr_of_eventuallyEq
    filter_upwards [hsol] with t ht
    exact ht i
  have hzero := hconst.unique (hasDerivAt_const θ (-1 : ℂ))
  have hb := hbase i
  change u i - (m θ i)^2 * ∑ j, (S i j : ℂ) * u j = z' * (m θ i)^2
  linear_combination -(m θ i) * hzero - (u i) * hb

/-- The normalized quadratic residual is equivalent to the original
polynomial equation after the signed diagonal change of variables. -/
theorem scalar_normalized_to_polynomial (m p q B T w H : ℂ)
    (hp : p ^ 2 = 1) (hq : q = p * m) (hb : (-1 : ℂ) = m * B)
    (hr : H - q*T = p*H*(q*T) + q*(1+p*H)*w) :
    (-1 : ℂ) = (m+q*H)*(B+w+T) := by
  subst q
  linear_combination (1+p*H)*hb + p*hr + m*(1+p*H)*(T+w)*hp

/-- Reverse direction of the normalization: every point constructed by the
analytic implicit-function theorem is an actual Dyson polynomial solution. -/
theorem normalized_residual_polynomial_solution
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ w : ℂ)
    (m p q H : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hm : PolynomialDyson.IsPolynomialSolution S a τ m)
    (hres : H - F H = Singularities.normalizedNonlinearity F.toLinearMap p q H (fun _ => w)) :
    PolynomialDyson.IsPolynomialSolution S a (τ+w) (fun i => m i+q i*H i) := by
  intro i
  have hr := congrFun hres i
  simp only [Singularities.normalizedNonlinearity, ContinuousLinearMap.coe_coe, Pi.sub_apply] at hr
  rw [hF H] at hr
  change H i - q i * (∑ j, (S i j : ℂ) * (q j * H j)) =
    p i * H i * (q i * (∑ j, (S i j : ℂ) * (q j * H j))) +
      q i * (1 + p i * H i) * w at hr
  have hh := scalar_normalized_to_polynomial (m i) (p i) (q i)
    (τ-(a i : ℂ)+∑ j, (S i j : ℂ)*m j)
    (∑ j, (S i j : ℂ)*(q j*H j)) w (H i) (hp i) (hq i) (hm i) hr
  convert hh using 1 <;> simp only [mul_add, Finset.sum_add_distrib] <;> ring

/-- The actual curve `m₀+qH` constructed from the normalized graph solves
the original polynomial system near the singular point. -/
theorem normalized_curve_polynomial
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℂ)
    (m p q : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hm : PolynomialDyson.IsPolynomialSolution S a τ m)
    (curve : ℂ → ℂ × (ι → ℂ))
    (hres : ∀ᶠ θ in 𝓝 (0 : ℂ), (curve θ).2 - F (curve θ).2 =
      Singularities.normalizedNonlinearity F.toLinearMap p q (curve θ).2
        (fun _ => (curve θ).1)) :
    ∀ᶠ θ in 𝓝 (0 : ℂ), PolynomialDyson.IsPolynomialSolution S a (τ+(curve θ).1)
      (fun i => m i+q i*(curve θ).2 i) := by
  filter_upwards [hres] with θ hθ
  exact normalized_residual_polynomial_solution S a τ (curve θ).1 m p q (curve θ).2 F
    hp hq hF hm hθ

/-- Differential stability identity along the constructed normalized curve,
with its actual diagonal change of variables. -/
theorem normalized_curve_stability_identity
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℂ)
    (m p q : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hm : PolynomialDyson.IsPolynomialSolution S a τ m)
    (curve : ℂ → ℂ × (ι → ℂ)) (θ Ω' : ℂ) (H' : ι → ℂ)
    (hc : HasDerivAt curve (Ω', H') θ)
    (hres : ∀ᶠ t in 𝓝 θ, (curve t).2 - F (curve t).2 =
      Singularities.normalizedNonlinearity F.toLinearMap p q (curve t).2
        (fun _ => (curve t).1)) :
    InteriorStability.stabilityOperator S (fun i => m i+q i*(curve θ).2 i)
      (fun i => q i*H' i) = fun i => Ω' * (m i+q i*(curve θ).2 i)^2 := by
  have hmc : HasDerivAt (fun t i => m i+q i*(curve t).2 i) (fun i => q i*H' i) θ := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_pi.mp hc.snd) i).const_mul (q i) |>.const_add (m i)
  apply dyson_curve_derivative S a (fun t => τ+(curve t).1)
    (fun t i => m i+q i*(curve t).2 i) θ Ω' (fun i => q i*H' i)
    (hc.fst.const_add τ) hmc
  filter_upwards [hres] with t ht
  exact normalized_residual_polynomial_solution S a τ (curve t).1 m p q (curve t).2 F
    hp hq hF hm ht

/-- The exact tangent identity gives the lower inverse bound on the
singular direction, with no eigenvector perturbation assumption. -/
theorem inverse_norm_lower_from_tangent
    (S : Matrix ι ι ℝ) (m u : ι → ℂ) (ω : ℂ)
    (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ))
    (he : ∀ v, e v = InteriorStability.stabilityOperator S m v)
    (ht : InteriorStability.stabilityOperator S m u = fun i => ω*(m i)^2) :
    ‖u‖ ≤ ‖(e.symm : (ι → ℂ) →L[ℂ] (ι → ℂ))‖ *
      (‖ω‖ * ‖fun i => (m i)^2‖) := by
  have hu : u = e.symm (ω • (fun i => (m i)^2)) := by
    apply e.injective
    simpa only [e.apply_symm_apply, he, Pi.smul_apply, smul_eq_mul] using ht
  calc
    ‖u‖ = ‖e.symm (ω • (fun i => (m i)^2))‖ := congrArg norm hu
    _ ≤ ‖(e.symm : (ι → ℂ) →L[ℂ] (ι → ℂ))‖ * ‖ω • (fun i => (m i)^2)‖ :=
      (e.symm : (ι → ℂ) →L[ℂ] (ι → ℂ)).le_opNorm _
    _ = _ := by rw [norm_smul]

end NonSymmetricDyson.Full.SingularLinear
