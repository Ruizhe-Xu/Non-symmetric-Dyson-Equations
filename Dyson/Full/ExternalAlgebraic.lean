import Mathlib
import Dyson.LocalSolvability
import Dyson.GlobalWellPosedness

/-!
# The polynomial Jacobian criterion, and its application to Dyson equations

`JacobianAlgebraicity` is an explicit external theorem parameter.  It applies
to *any* finite polynomial system and any holomorphic branch on the upper
half-plane.  Its mathematical inputs are the algebraic Jacobian criterion,
dimension = transcendence degree, and the analytic identity theorem.

The Dyson polynomial, the equality with the residual, the vanishing of that
residual, and invertibility of the derivative are proved in Lean.  In
particular coordinate algebraicity is not an assumed property of the Dyson
solution.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.ExternalAlgebraic

abbrev upper : Set ℂ := {z | 0 < z.im}

/-- A nonzero bivariate polynomial relation of positive degree in the value
variable. `false` denotes the base variable, and `true` the value variable. -/
def AlgebraicOnUpper (f : ℂ → ℂ) : Prop :=
  ∃ p : MvPolynomial Bool ℂ, p ≠ 0 ∧ 0 < p.degreeOf true ∧
    ∀ z ∈ upper, MvPolynomial.eval (fun b => if b then f z else z) p = 0

variable {ι : Type*} [Fintype ι]

/-- Evaluation of a polynomial in a base coordinate and finitely many
dependent coordinates. -/
def evaluateSystem (P : ι → MvPolynomial (Option ι) ℂ)
    (p : ℂ × (ι → ℂ)) : ι → ℂ :=
  fun i => MvPolynomial.eval (fun o => o.elim p.1 p.2) (P i)

def augmentedPolynomialMap (P : ι → MvPolynomial (Option ι) ℂ)
    (p : ℂ × (ι → ℂ)) : ℂ × (ι → ℂ) :=
  (p.1, evaluateSystem P p)

/-- The external algebraic/analytic theorem used here.  All hypotheses are
on an arbitrary polynomial system and its actual derivative.  Using the
augmented derivative is equivalent to invertibility of the Jacobian in the
dependent coordinates. -/
def JacobianAlgebraicity : Prop :=
  ∀ (P : ι → MvPolynomial (Option ι) ℂ) (f : ℂ → ι → ℂ)
    (z₀ : ℂ) (L : (ℂ × (ι → ℂ)) →L[ℂ] (ℂ × (ι → ℂ))),
    0 < z₀.im → AnalyticOnNhd ℂ f upper →
    (∀ z ∈ upper, evaluateSystem P (z, f z) = 0) →
    HasStrictFDerivAt (augmentedPolynomialMap P) L (z₀, f z₀) →
    Function.Bijective L → ∀ i, AlgebraicOnUpper (fun z => f z i)

/-- The manuscript's denominator-free polynomials, now as actual elements
of a multivariable polynomial ring. -/
def dysonPolynomial (S : Matrix ι ι ℝ) (a : ι → ℝ) (i : ι) :
    MvPolynomial (Option ι) ℂ :=
  1 + MvPolynomial.X (some i) *
    (MvPolynomial.X none +
      ∑ j, MvPolynomial.C (S i j : ℂ) * MvPolynomial.X (some j) -
      MvPolynomial.C (a i : ℂ))

theorem evaluate_dysonPolynomial (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : ℂ × (ι → ℂ)) :
    evaluateSystem (dysonPolynomial S a) p =
      LocalSolvability.polynomialResidual S a p := by
  ext i
  simp [evaluateSystem, dysonPolynomial, LocalSolvability.polynomialResidual]

theorem augmented_dysonPolynomial (S : Matrix ι ι ℝ) (a : ι → ℝ) :
    augmentedPolynomialMap (dysonPolynomial S a) =
      LocalSolvability.totalMap S a := by
  funext p
  exact Prod.ext rfl (evaluate_dysonPolynomial S a p)

/-- Coordinate algebraicity follows for every actual upper-half-plane
solution family.  Neither boundary regularity nor irreducibility is used. -/
theorem solution_algebraic (external : JacobianAlgebraicity (ι := ι))
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (f : ℂ → ι → ℂ)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (f z))
    (heq : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (f z)) :
    ∀ i, AlgebraicOnUpper (fun z => f z i) := by
  have hI : 0 < Complex.I.im := by simp
  refine external (dysonPolynomial S a) f Complex.I
    (LocalSolvability.totalDerivative S a (Complex.I, f Complex.I)) hI
    (LocalSolvability.analyticOnNhd_of_solution_family S a f hS hupper heq) ?_ ?_ ?_
  · intro z hz
    rw [evaluate_dysonPolynomial]
    exact (LocalSolvability.polynomialResidual_zero_iff S a z (f z)
      (BasicEstimates.component_ne_zero (hupper z hz))).mpr (heq z hz)
  · rw [augmented_dysonPolynomial]
    exact LocalSolvability.totalMap_hasStrictFDerivAt S a (Complex.I, f Complex.I)
  · exact LocalSolvability.totalDerivative_bijective S a Complex.I (f Complex.I)
      hS hI (hupper _ hI) (heq _ hI)

end NonSymmetricDyson.Full.ExternalAlgebraic

namespace NonSymmetricDyson.Full.ExternalAlgebraic

abbrev closedUpper : Set ℂ := {z | 0 ≤ z.im}

def ray (τ r θ : ℝ) : ℂ :=
  (τ : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- A convergent Puiseux expansion in a specified root chart. The analytic
factor has a genuinely convergent Taylor series (`AnalyticAt`), and its
constant coefficient is nonzero. The root is continuous on the *closed*
upper half-plane, and its phase is specified on every upper ray.

`leading_ray` records the immediate leading-term limit of that convergent
series. It makes no assertion about signs, poles, atoms, boundary values,
support, or Hölder regularity of `f`. -/
structure PuiseuxChart (f : ℂ → ℂ) (τ : ℝ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  exponent : ℤ
  root : ℂ → ℂ
  root_continuous : ContinuousOn root closedUpper
  root_center : root (τ : ℂ) = 0
  root_power : ∀ z ∈ closedUpper, root z ^ denominator = z - (τ : ℂ)
  root_ray : ∀ (r θ : ℝ), 0 < r → θ ∈ Icc (0 : ℝ) Real.pi →
    root (ray τ r θ) = ((r ^ (1 / (denominator : ℝ)) : ℝ) : ℂ) *
      Complex.exp (((θ / (denominator : ℝ) : ℝ) : ℂ) * Complex.I)
  factor : ℂ → ℂ
  factor_analytic : AnalyticAt ℂ factor 0
  factor_ne_zero : factor 0 ≠ 0
  radius : ℝ
  radius_pos : 0 < radius
  expansion : ∀ z ∈ upper, ‖z - (τ : ℂ)‖ < radius →
    f z = root z ^ exponent * factor (root z)
  leading_ray : ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
    Tendsto (fun r : ℝ => ((r ^ (-(exponent : ℝ) / (denominator : ℝ)) : ℝ) : ℂ) * f (ray τ r θ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (factor 0 * Complex.exp
        ((((exponent : ℝ) / (denominator : ℝ) * θ : ℝ) : ℂ) * Complex.I)))

/-- A holomorphic extension near one real point, expressed as equality on
the upper portion of an actual neighborhood. -/
def HolomorphicAcross (f : ℂ → ℂ) (τ : ℝ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    ∀ᶠ z in 𝓝 (τ : ℂ), z ∈ upper → f z = g z

/-- The external convergent Newton--Puiseux theorem. This theorem concerns
arbitrary holomorphic algebraic scalar functions. The exceptional set and
root expansions are its conclusions; all Dyson consequences are proved
separately. No claim about the sign of a leading coefficient is an input. -/
def ConvergentPuiseuxTheory : Prop :=
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f upper → AlgebraicOnUpper f →
    (∃ z ∈ upper, f z ≠ 0) →
    (∃ E : Set ℝ, E.Finite ∧ ∀ τ ∉ E, HolomorphicAcross f τ) ∧
    (∀ τ : ℝ, Nonempty (PuiseuxChart f τ))

end NonSymmetricDyson.Full.ExternalAlgebraic
