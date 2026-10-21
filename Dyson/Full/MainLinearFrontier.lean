import Dyson.Full.MainLinearSingular
import Dyson.Full.SingularPhysicalInverse
import Dyson.Full.MainSingularities

/-! M6 at actual regular singularities: construct the physical edge/cusp
normal form, derive its local inverse rate, and extend that rate through the
whole vertical strip. All local Dyson data are conclusions. -/
noncomputable section
open scoped Topology
namespace NonSymmetricDyson.Full.MainLinearSingular
open Singularities ExternalAlgebraic SingularLinear

/-- Both fractional exponents of the actual normal form are strictly positive. -/
theorem inverseExponent_cases {n : ℕ} (hk : n = 2 ∨ n = 3) :
    inverseExponent n = (1:ℝ)/2 ∨ inverseExponent n = (2:ℝ)/3 := by
  rcases hk with rfl | rfl <;> norm_num [inverseExponent]

/-- The full-height singular estimate for a constructed physical normal form,
with its degree retained to identify the edge/cusp exponent. -/
theorem regular_frontier_normal_form_full_strip
    (perron : ExternalPerronExistence) {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (nf : PhysicalNormalForm S a τ m (fun j => (Boundary.boundaryVector m (τ : ℂ) j).re)) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^inverseExponent nf.degree) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^inverseExponent nf.degree) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨c,C,hc,hC,hlocal⟩ := regular_frontier_normal_form_inverse perron hn algebraic
    puiseux S a hS hirr m hupper heq τ i hfront hτ nf
  have hα : 0 < inverseExponent nf.degree := by
    rcases inverseExponent_cases nf.degree_cases with h | h <;> rw [h] <;> norm_num
  exact singular_full_height_of_eventual S a m hS hupper heq τ (inverseExponent nf.degree)
    c C hα hc hC hlocal

/-- M6 singular clause, starting only from the actual Dyson model and an
actual regular frontier point. The exponent is one half at a quadratic edge
or two thirds at a cubic cusp; the strip estimate holds for every η>0. -/
theorem main_theorem_six_singular_strip
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ α δ c C : ℝ, (α = (1:ℝ)/2 ∨ α = (2:ℝ)/3) ∧
      0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^α) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^α) := by
  obtain ⟨nf⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  obtain ⟨δ,c,C,hδ,hc,hC,hbound⟩ := regular_frontier_normal_form_full_strip perron hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ nf
  exact ⟨inverseExponent nf.degree,δ,c,C,inverseExponent_cases nf.degree_cases,hδ,hc,hC,hbound⟩

end NonSymmetricDyson.Full.MainLinearSingular
