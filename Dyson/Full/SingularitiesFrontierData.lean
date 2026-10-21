import Dyson.Full.PerronStable
import Dyson.Full.BoundaryEdges

/-! Complete singularity input data at an actual regular frontier of the
Dyson support. All signs, Perron vectors, the real stable coefficient, and
quadratic/cubic nondegeneracy are derived, rather than added as local data
assumptions. The only external premises are the separately stated general
algebraicity, Puiseux, and Perron--Frobenius theorems. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Full.Singularities

/-- Concrete data attached to the actual boundary vector. -/
structure FrontierData {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (m₀ : Fin n → ℂ) where
  p : Fin n → ℝ
  r : Fin n → ℝ
  l : Fin n → ℝ
  u : Fin n → ℝ
  K : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)
  real_value : ∀ i, (m₀ i).im = 0
  nonzero : ∀ i, m₀ i ≠ 0
  sign_square : ∀ i, p i ^ 2 = 1
  norm_sign : ∀ i, ‖m₀ i‖ = p i * (m₀ i).re
  right_positive : ∀ i, 0 < r i
  left_positive : ∀ i, 0 < l i
  normalized : ∑ i, l i * r i = 1
  right_fixed : ∀ i, ∑ j, saturatedMatrix S m₀ i j * r j = r i
  left_fixed : ∀ j, ∑ i, l i * saturatedMatrix S m₀ i j = l j
  simple : ∀ x : Fin n → ℂ, complexMatrixOperator (saturatedMatrix S m₀) x = x →
    x = complexFunctional l x • (fun i => (r i : ℂ))
  restricted : IsRestrictedInverse (complexMatrixOperator (saturatedMatrix S m₀)).toLinearMap K
    (complexFunctional l).toLinearMap (fun i => (r i : ℂ))
  quadratic_image : K (fun i => (p i : ℂ) * (r i : ℂ)^2) = (fun i => (u i : ℂ))
  orthogonal : ∑ i, l i * u i = 0
  stable_equation : ∀ i, u i - ∑ j, saturatedMatrix S m₀ i j * u j =
    p i * r i^2 - r i * quadraticCoefficient p l r
  quadratic_bridge : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ)^2) =
    (quadraticCoefficient p l r : ℂ)
  cubic_bridge : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ) *
    (complexMatrixOperator (saturatedMatrix S m₀) (K (fun j => (p j : ℂ) * (r j : ℂ)^2)) i +
      K (fun j => (p j : ℂ) * (r j : ℂ)^2) i)) =
      (cubicCoefficient (saturatedMatrix S m₀) p l r u : ℂ)
  nondegenerate : quadraticCoefficient p l r ≠ 0 ∨
    0 < cubicCoefficient (saturatedMatrix S m₀) p l r u

/-- The actual regular frontier supplies all local singularity data. In
particular nondegeneracy is derived using genuine positive-density boundary
solutions converging to the frontier point, not an assumed physical sequence. -/
theorem regular_frontier_data (external : ExternalPerronExistence)
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
    Nonempty (FrontierData S (Boundary.boundaryVector m (τ : ℂ))) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  let b : Fin n → ℝ := fun j => (m₀ j).re
  let q : Fin n → ℝ := fun j => ‖m₀ j‖
  let p : Fin n → ℝ := fun j => b j / q j
  have hreal : ∀ j, (m₀ j).im = 0 :=
    Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hboundary := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hnz : ∀ j, m₀ j ≠ 0 := hboundary.1
  have hcast : (fun j => (b j : ℂ)) = m₀ := by
    funext j
    apply Complex.ext
    · rfl
    · simp [hreal]
  have hqpos : ∀ j, 0 < q j := fun j => norm_pos_iff.mpr (hnz j)
  have hqabs (j : Fin n) : q j = |b j| := by
    dsimp [q]
    rw [← congrFun hcast j, Complex.norm_real, Real.norm_eq_abs]
  have hq2 (j : Fin n) : q j ^ 2 = b j ^ 2 := by rw [hqabs, sq_abs]
  have hp2 (j : Fin n) : p j ^ 2 = 1 := by
    dsimp [p]
    rw [div_pow, ← hq2, div_self (pow_ne_zero 2 (hqpos j).ne')]
  have hpq (j : Fin n) : q j = p j * b j := by
    dsimp [p]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hqpos j).ne').mpr
    convert hq2 j using 1 <;> ring
  obtain ⟨r, l, hr, hl, hnorm, hFr, hlF, hsimple⟩ :=
    regular_frontier_perron_data external hn algebraic puiseux S a hS hirr m hupper heq
      τ i hfront hτ
  obtain ⟨K, u, hK, huK, hul, hu, hσ, hψ⟩ :=
    quadratic_stable_data_exists (saturatedMatrix S m₀) p r l hnorm hFr hlF hsimple
  obtain ⟨E, hE, _, hpos, hsol, hlim⟩ :=
    Boundary.regular_frontier_sequence hn algebraic puiseux S a hS hirr m hupper heq
      τ i hfront hτ
  let w : ℕ → ℂ := fun k => (E k : ℂ) - (τ : ℂ)
  let g : ℕ → Fin n → ℂ := fun k => Boundary.boundaryVector m (E k : ℂ)
  have hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ) (fun j => (b j : ℂ)) := by
    rw [hcast]
    exact PolynomialDyson.of_dyson hboundary.2.2 hnz
  have hphysical (k : ℕ) : PolynomialDyson.IsPolynomialSolution S a ((τ : ℂ) + w k) (g k) := by
    have henergy : (τ : ℂ) + w k = (E k : ℂ) := by dsimp [w]; ring
    rw [henergy]
    exact PolynomialDyson.of_dyson (hsol k) (BasicEstimates.component_ne_zero (hpos k))
  have hwlim : Tendsto w atTop (𝓝 (0 : ℂ)) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hE).sub_const (τ : ℂ)
    simpa [w] using hh
  have hconv : Tendsto (fun k => (w k, g k)) atTop
      (𝓝 (0, fun j => (b j : ℂ))) := by
    rw [hcast]
    exact hwlim.prodMk_nhds hlim
  have hw (k : ℕ) : w k ≠ 0 := by
    intro hk
    have hEt : E k = τ := Complex.ofReal_injective (sub_eq_zero.mp hk)
    have hh := hpos k i
    rw [hEt] at hh
    exact (ne_of_gt hh) (hreal i)
  have hnondeg := singularity_coefficients_nondegenerate S (saturatedMatrix S m₀) a (τ : ℂ)
    b p q r l u hS hp2 hpq hqpos hr hl (fun _ _ => rfl) hFr hlF hnorm hsimple hu
    hbase w g hphysical hconv hw
  exact ⟨⟨p, r, l, u, K, hreal, hnz, hp2, hpq, hr, hl, hnorm, hFr, hlF,
    hsimple, hK, huK, hul, hu, hσ, hψ, hnondeg⟩⟩

end NonSymmetricDyson.Full.Singularities
