import Mathlib

/-!
# Exact algebraic identities for the vector Dyson equation

Source: `main-article-1014.tex`, version uploaded 2026-10-19.
This file proves only the explicitly listed algebraic steps; it does not claim
existence, uniqueness, spectral stability, singularity asymptotics, or analytic
implicit-function statements from the manuscript.

The coefficient field is arbitrary. The operator `S` is a linear map on a
coordinate space, which includes every finite matrix acting on vectors.
-/

namespace DysonPaper.Algebra

variable {K ι : Type*} [Field K]

/-- Multiplication by a coordinate function. -/
def coordMul (a x : ι → K) : ι → K := fun i => a i * x i

/-- Action of the original linearized stability operator `I - diag(m²) S`. -/
def stabilityAction (m : ι → K) (S : (ι → K) →ₗ[K] (ι → K))
    (u : ι → K) : ι → K := fun i => u i - m i ^ 2 * S u i

/-- The scaled operator `F = diag(q) S diag(q)`. In the manuscript `q = |m|`. -/
def scaledOperator (q : ι → K) (S : (ι → K) →ₗ[K] (ι → K))
    (h : ι → K) : ι → K := coordMul q (S (coordMul q h))

/-- Action of `U - F`, with `Uᵢ = qᵢ²/mᵢ²`. -/
def phaseStabilityAction (m q : ι → K) (S : (ι → K) →ₗ[K] (ι → K))
    (h : ι → K) : ι → K :=
  fun i => q i ^ 2 / m i ^ 2 * h i - scaledOperator q S h i

/-- Scalar reciprocal subtraction, including all denominators explicitly.
This is the algebra underlying the manuscript's exact displacement identity. -/
theorem scalar_dyson_product (m g b sm sg r : K)
    (hm0 : m ≠ 0) (hg0 : g ≠ 0)
    (hm : -m⁻¹ = b + sm) (hg : -g⁻¹ = b + sg + r) :
    g - m = m * g * (sg - sm + r) := by
  have hdiff : (g - m) / (m * g) = sg - sm + r := by
    calc
      (g - m) / (m * g) = -g⁻¹ - (-m⁻¹) := by
        field_simp [hm0, hg0]
        ring
      _ = sg - sm + r := by rw [hm, hg]; ring
  calc
    g - m = (sg - sm + r) * (m * g) :=
      (div_eq_iff (mul_ne_zero hm0 hg0)).mp hdiff
    _ = m * g * (sg - sm + r) := mul_comm _ _

/-- Exact scalar displacement equation; no smallness hypothesis is needed. -/
theorem scalar_dyson_displacement (m g b sm sg r : K)
    (hm0 : m ≠ 0) (hg0 : g ≠ 0)
    (hm : -m⁻¹ = b + sm) (hg : -g⁻¹ = b + sg + r) :
    (g - m) - m ^ 2 * (sg - sm) = m ^ 2 * r + (g - m) ^ 2 / g := by
  have hprod := scalar_dyson_product m g b sm sg r hm0 hg0 hm hg
  have hid :
      ((g - m) - m ^ 2 * (sg - sm)) -
          (m ^ 2 * r + (g - m) ^ 2 / g) =
        m / g * ((g - m) - m * g * (sg - sm + r)) := by
    field_simp [hg0]
    ring
  apply sub_eq_zero.mp
  rw [hid, hprod, sub_self, mul_zero]

/-- Manuscript lines 507–512 and equation
`e:bootstrap-exact-dyson-expansion`, lines 5152–5155.
The background term `b` represents `z 1 - a`. All coordinates of both
solutions must be nonzero, as required for the displayed reciprocal equations. -/
theorem dyson_displacement (m g b r : ι → K)
    (S : (ι → K) →ₗ[K] (ι → K))
    (hm0 : ∀ i, m i ≠ 0) (hg0 : ∀ i, g i ≠ 0)
    (hm : ∀ i, -(m i)⁻¹ = b i + S m i)
    (hg : ∀ i, -(g i)⁻¹ = b i + S g i + r i) :
    stabilityAction m S (g - m) =
      fun i => m i ^ 2 * r i + (g i - m i) ^ 2 / g i := by
  ext i
  simp only [stabilityAction, map_sub, Pi.sub_apply]
  exact scalar_dyson_displacement (m i) (g i) (b i) (S m i)
    (S g i) (r i) (hm0 i) (hg0 i) (hm i) (hg i)

/-- Manuscript `eq.I-m2S-transform`, lines 546–551, as an identity on vectors.
`q` is any nonzero diagonal scaling; taking `qᵢ = |mᵢ|` gives the manuscript
factorization. This theorem does not assume or prove any norm bound. -/
theorem stability_diagonal_factorization (m q u : ι → K)
    (S : (ι → K) →ₗ[K] (ι → K))
    (hm0 : ∀ i, m i ≠ 0) (hq0 : ∀ i, q i ≠ 0) :
    stabilityAction m S u =
      fun i => m i ^ 2 / q i *
        phaseStabilityAction m q S (fun j => u j / q j) i := by
  have hcancel : coordMul q (fun j => u j / q j) = u := by
    ext j
    simp only [coordMul]
    field_simp [hq0 j]
  ext i
  change u i - m i ^ 2 * S u i = m i ^ 2 / q i *
    (q i ^ 2 / m i ^ 2 * (u i / q i) -
      q i * S (coordMul q (fun j => u j / q j)) i)
  rw [hcancel]
  field_simp [hm0 i, hq0 i]

/-- Algebraic form of the manuscript's normalized boundary equation.
At a real boundary point, `p² = 1`, `q = p m`, and `g = m + q h`.
The hypotheses keep these real-boundary properties explicit. -/
theorem scalar_normalized_quadratic (m g b sm sg ξ p q h : K)
    (hm0 : m ≠ 0) (hg0 : g ≠ 0) (hq0 : q ≠ 0)
    (hp : p ^ 2 = 1) (hq : q = p * m) (hgm : g = m + q * h)
    (hm : -m⁻¹ = b + sm) (hg : -g⁻¹ = b + sg + ξ) :
    h - q * (sg - sm) =
      p * h * (q * (sg - sm)) + q * (1 + p * h) * ξ := by
  have hprod := scalar_dyson_product m g b sm sg ξ hm0 hg0 hm hg
  have hmg : m * g = q * (q * (1 + p * h)) := by
    rw [hgm, hq]
    linear_combination -m ^ 2 * (1 + p * h) * hp
  have hh : h = q * (1 + p * h) * (sg - sm + ξ) := by
    apply mul_left_cancel₀ hq0
    calc
      q * h = g - m := by rw [hgm]; ring
      _ = m * g * (sg - sm + ξ) := hprod
      _ = q * (q * (1 + p * h) * (sg - sm + ξ)) := by rw [hmg]; ring
  linear_combination hh

/-- Manuscript `e:abstract-exact-quadratic-equation`, lines 5386–5389.
This formalizes the exact quadratic identity before projecting to the stable
and unstable subspaces. It does not claim a cubic reduction or analytic
existence of the stable component. -/
theorem normalized_quadratic_equation (m g b ξ p q h : ι → K)
    (S : (ι → K) →ₗ[K] (ι → K))
    (hm0 : ∀ i, m i ≠ 0) (hg0 : ∀ i, g i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hgm : g = m + coordMul q h)
    (hm : ∀ i, -(m i)⁻¹ = b i + S m i)
    (hg : ∀ i, -(g i)⁻¹ = b i + S g i + ξ i) :
    h - scaledOperator q S h =
      fun i => p i * h i * scaledOperator q S h i +
        q i * (1 + p i * h i) * ξ i := by
  have hlin : S g - S m = S (coordMul q h) := by
    rw [hgm, map_add]
    simp
  ext i
  have hpoint : g i = m i + q i * h i := by
    simpa only [Pi.add_apply, coordMul] using congrFun hgm i
  have hpointlin : S g i - S m i = S (coordMul q h) i := congrFun hlin i
  have heq := scalar_normalized_quadratic (m i) (g i) (b i)
    (S m i) (S g i) (ξ i) (p i) (q i) (h i)
    (hm0 i) (hg0 i) (hq0 i) (hp i) (hq i) hpoint (hm i) (hg i)
  simpa only [hpointlin, Pi.sub_apply, scaledOperator, coordMul] using heq

end DysonPaper.Algebra
