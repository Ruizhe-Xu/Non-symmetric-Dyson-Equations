import Dyson.Full.SingularitiesDensityClassification
import Dyson.Full.BoundaryLocalLimits

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- Conversion from imaginary parts to the probability density with the
standard Stieltjes normalization 1/π. -/
theorem density_normalize_error (v D C t : ℝ)
    (h : |v - D * t| ≤ C * t ^ 2) :
    |v / Real.pi - (D / Real.pi) * t| ≤ (C / Real.pi) * t ^ 2 := by
  have he : v / Real.pi - (D / Real.pi) * t = (v - D * t) / Real.pi := by ring
  rw [he, abs_div, abs_of_pos Real.pi_pos]
  calc
    |v - D * t| / Real.pi ≤ (C * t ^ 2) / Real.pi :=
      div_le_div_of_nonneg_right h Real.pi_pos.le
    _ = (C / Real.pi) * t ^ 2 := by ring

/-- M5 for the actual densities: exactly a one-sided square-root edge or a
two-sided cubic cusp, with positive leading coefficients and quantitative
second-order remainder. All seven model-specific ingredients (real boundary,
Perron value one, stable inverse, σ/ψ, nondegeneracy, physical root, and density
selection) are proved internally. External parameters are universal classical
algebraic/analytic/Perron statements only. -/
theorem main_theorem_five
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
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
    ∃ (c : ℝ) (D : Fin n → ℝ) (C : ℝ), c ≠ 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ((∀ᶠ x in 𝓝 τ, ∀ j,
        (c * (x - τ) < 0 →
          |Boundary.realDensity m j x - D j * rootRadius c 2 (x - τ)| ≤
            C * (rootRadius c 2 (x - τ)) ^ 2 ∧ 0 < Boundary.realDensity m j x) ∧
        (0 < c * (x - τ) → Boundary.realDensity m j x = 0)) ∨
      (c < 0 ∧ ∀ᶠ x in 𝓝 τ, ∀ j,
        |Boundary.realDensity m j x - D j * rootRadius c 3 (x - τ)| ≤
          C * (rootRadius c 3 (x - τ)) ^ 2 ∧
        (x ≠ τ → 0 < Boundary.realDensity m j x))) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨P⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  let b : ℝ → Fin n → ℂ := fun x => Boundary.boundaryVector m (x : ℂ)
  have hb0 : b τ = (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  have hblim : ∀ᶠ x : ℝ in 𝓝 τ,
      Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (b x)) :=
    hblocal.mono fun _ h => h.2
  rcases P.degree_cases with hk | hk
  · refine ⟨P.coefficient, fun j => P.tangent j / Real.pi, P.errorConstant / Real.pi,
      P.coefficient_ne_zero, fun j => div_pos (P.tangent_pos j) Real.pi_pos,
      div_pos P.errorConstant_pos Real.pi_pos, Or.inl ?_⟩
    filter_upwards [P.quadratic_boundary_density hk b hb0 hbcont hblim] with x hx j
    constructor
    · intro hs
      have hh := hx j |>.1 hs
      exact ⟨density_normalize_error _ _ _ _ hh.1, div_pos hh.2 Real.pi_pos⟩
    · intro hs
      exact div_eq_zero_iff.mpr (Or.inl ((hx j).2 hs))
  · refine ⟨P.coefficient, fun j => (P.tangent j * (Real.sqrt 3 / 2)) / Real.pi,
      P.errorConstant / Real.pi, P.coefficient_ne_zero, ?_,
      div_pos P.errorConstant_pos Real.pi_pos, Or.inr ⟨P.cubic_negative hk, ?_⟩⟩
    · intro j
      exact div_pos (mul_pos (P.tangent_pos j)
        (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))) Real.pi_pos
    · filter_upwards [P.cubic_boundary_density hk b hb0 hbcont hblim] with x hx j
      exact ⟨density_normalize_error _ _ _ _ (hx j).1,
        fun hne => div_pos ((hx j).2 hne) Real.pi_pos⟩

end NonSymmetricDyson.Full.Singularities
