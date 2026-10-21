import Dyson.Full.SingularitiesCubic
import Dyson.Full.MainSingularities
import Dyson.Full.BoundaryLocalLimits

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.Singularities

/-- The canonical scalar coordinate of the actual boundary solution. -/
def boundaryCoordinate {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (m : ℂ → Fin n → ℂ) (τ : ℝ)
    (D : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) (x : ℝ) : ℂ :=
  complexFunctional D.l (fun j =>
    (Boundary.boundaryVector m (x : ℂ) j - Boundary.boundaryVector m (τ : ℂ) j) /
      (‖Boundary.boundaryVector m (τ : ℂ) j‖ : ℂ))

/-- The original cubic proposition for the actual boundary solution. The
quadratic and cubic coefficients are the computed Perron coefficients;
the scalar error has the sharpened mixed bound, including its imaginary part. -/
theorem frontier_data_cubic_error
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m)
    (D : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) :
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro m₀ μ σ ψ Θ e
  let q : Fin n → ℂ := fun j => (‖m₀ j‖ : ℂ)
  let p : Fin n → ℂ := fun j => (D.p j : ℂ)
  let r : Fin n → ℂ := fun j => (D.r j : ℂ)
  let F := complexMatrixOperator (saturatedMatrix S m₀)
  let ℓ := complexFunctional D.l
  have hqpos : ∀ j, 0 < ‖m₀ j‖ := fun j => norm_pos_iff.mpr (D.nonzero j)
  have hq0 : ∀ j, q j ≠ 0 := fun j => by dsimp [q]; exact_mod_cast (hqpos j).ne'
  have hμpos : 0 < μ := Finset.sum_pos (fun j _ => mul_pos (D.left_positive j) (hqpos j)) Finset.univ_nonempty
  have hμeq : ℓ q = (μ : ℂ) := by simp [ℓ, q, complexFunctional_apply, μ]
  have hFr : F r = r := by
    ext j
    simp only [F, r, complexMatrixOperator_apply]
    exact_mod_cast D.right_fixed j
  have hnorm : ℓ r = 1 := by
    dsimp [ℓ, r]
    rw [complexFunctional_apply]
    exact_mod_cast D.normalized
  have hFreal : ∀ x, F (star x) = star (F x) := by
    intro x
    ext j
    simp [F, complexMatrixOperator_apply]
  have hℓreal : ∀ x, ℓ (star x) = star (ℓ x) := by
    intro x
    simp [ℓ, complexFunctional_apply]
  have hσ : ℓ (p * r * r) = (σ : ℂ) := by
    simpa only [p, r, ℓ, pow_two, mul_assoc] using D.quadratic_bridge
  have hψ : ℓ (p * r * (F (D.K (p * r * r)) + D.K (p * r * r))) = (ψ : ℂ) := by
    simpa only [p, r, ℓ, F, pow_two, mul_assoc] using D.cubic_bridge
  obtain ⟨C, hC, hc⟩ := normalized_cubic_error_neighborhood normalForm imaginaryOrder
    F D.K.toContinuousLinearMap ℓ p q r μ hμpos hμeq hFr hnorm
    (complexFunctional_left_eigenvector _ D.l D.left_fixed) D.simple D.restricted
    hFreal hℓreal (by ext j; simp [p]) (by ext j; simp [q]) σ ψ hσ hψ D.nondegenerate
  obtain ⟨hbcont, hbreg⟩ := Boundary.regular_boundary_continuous_and_limits algebraic puiseux S a hS m hupper heq τ hτ
  let h : ℝ → Fin n → ℂ := fun x j => (Boundary.boundaryVector m (x : ℂ) j - m₀ j) / q j
  have hh0 : h τ = 0 := by ext j; simp [h, m₀]
  have hhcont : ContinuousAt h τ := by
    apply continuousAt_pi.mpr
    intro j
    exact (((continuous_apply j).continuousAt.comp hbcont).sub continuousAt_const).div_const _
  have hvt : Tendsto (fun x : ℝ => (((x - τ : ℝ) : ℂ), h x)) (𝓝 τ) (𝓝 0) := by
    have hw : ContinuousAt (fun x : ℝ => ((x - τ : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    simpa [hh0] using hw.prodMk hhcont |>.tendsto
  have hcast : ∀ j, ((m₀ j).re : ℂ) = m₀ j := fun j => Complex.ext rfl (by simpa using (D.real_value j).symm)
  have hp : ∀ j, p j ^ 2 = 1 := fun j => by dsimp [p]; exact_mod_cast D.sign_square j
  have hq : ∀ j, q j = p j * m₀ j := by
    intro j
    rw [← hcast j]
    dsimp [q, p]
    exact_mod_cast D.norm_sign j
  have hF : ∀ v, F v = DysonPaper.Algebra.scaledOperator q (Model.action S) v := by
    intro v
    ext j
    simp only [F, complexMatrixOperator_apply, saturatedMatrix, Complex.ofReal_mul,
      DysonPaper.Algebra.scaledOperator, DysonPaper.Algebra.coordMul, q,
      Model.action_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hbe := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hbase := PolynomialDyson.of_dyson hbe.2.2 hbe.1
  refine ⟨hμpos, (1 + ‖q‖) * C, mul_pos (by positivity) hC, ?_⟩
  filter_upwards [hbreg, hvt.eventually hc] with x hx hc
  have hbx := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq x hx.1
  have hpoly : PolynomialDyson.IsPolynomialSolution S a
      ((τ : ℂ) + ((x - τ : ℝ) : ℂ)) (Boundary.boundaryVector m (x : ℂ)) := by
    simpa using PolynomialDyson.of_dyson hbx.2.2 hbx.1
  have hres := polynomial_solution_normalized_residual S a (τ : ℂ) ((x - τ : ℝ) : ℂ)
    m₀ (Boundary.boundaryVector m (x : ℂ)) p q F hp hq hq0 hF hbase hpoly
  have ht : ℓ (h x) = Θ x := rfl
  have hh := hc hres
  change ‖h x - ℓ (h x) • r‖ ≤ C * (‖ℓ (h x)‖ ^ 2 + ‖((x - τ : ℝ) : ℂ)‖) ∧ _ at hh
  rw [ht] at hh
  have him : 0 ≤ (Θ x).im := by
    change 0 ≤ (ℓ (h x)).im
    rw [complexFunctional_apply, Complex.im_sum]
    apply Finset.sum_nonneg
    intro j hj
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero]
    have he : (h x j).im = (Boundary.boundaryVector m (x : ℂ) j).im / ‖m₀ j‖ := by
      have hreal : (m₀ j).im = 0 := D.real_value j
      simp [h, q, Complex.div_ofReal_im, hreal]
    rw [he]
    exact mul_nonneg (D.left_positive j).le (div_nonneg (hbx.2.1 j) (hqpos j).le)
  have hCbig : C ≤ (1 + ‖q‖) * C := by nlinarith [norm_nonneg q]
  refine ⟨him, ?_, ?_, ?_⟩
  · intro j
    have he : Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x = q j * (h x - Θ x • r) j := by
      simp only [h, q, r, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hnz : (‖m₀ j‖ : ℂ) ≠ 0 := hq0 j
      field_simp [hnz]
      <;> ring
    rw [he, norm_mul]
    have hn := norm_le_pi_norm (h x - Θ x • r) j
    have hqnorm := norm_le_pi_norm q j
    have hmain := hh.1
    rw [Complex.norm_real, Real.norm_eq_abs] at hmain
    calc
      _ ≤ ‖q‖ * ‖h x - Θ x • r‖ := mul_le_mul hqnorm hn (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖q‖ * (C * (‖Θ x‖ ^ 2 + |x - τ|)) := mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hC.le (show 0 ≤ ‖Θ x‖ ^ 2 + |x - τ| by positivity)]
  · have hs := hh.2.1
    simpa only [e, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      hs.trans (mul_le_mul_of_nonneg_right hCbig (by positivity))
  · have hs := hh.2.2
    simpa only [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg him] using
      hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbig (norm_nonneg _)) (abs_nonneg _))


/-- All data in the cubic proposition are obtained from the actual regular
support frontier. No Perron, nondegeneracy, Taylor, or error assertion is
assumed in this application. -/
theorem regular_frontier_cubic_error
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  obtain ⟨D⟩ := regular_frontier_data perron hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  exact ⟨D, frontier_data_cubic_error normalForm imaginaryOrder hn algebraic puiseux S a hS m hupper heq τ hτ D⟩

end NonSymmetricDyson.Full.Singularities
