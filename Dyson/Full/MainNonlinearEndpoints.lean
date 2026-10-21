import Dyson.Full.MainNonlinearFrontier
import Dyson.Full.SingularityTopology

/-! M7 with the fractional exponent selected by the actual support topology. -/

noncomputable section
open scoped Topology
open Set

namespace NonSymmetricDyson.Full.Nonlinear
open Singularities

section Model

variable {n : ℕ}
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (ift : AnalyticImplicitFunctionPrinciple (Fin n → ℂ) (ℂ × (Fin n → ℂ)))
variable (rootArgument : AnalyticRootFactorizationPrinciple)
variable (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)

include perron normalForm orientation algebraic puiseux ift rootArgument hn hS hirr hupper heq hfront hτ

/-- The square-root denominator at a genuine one-sided regular edge. -/
theorem main_theorem_seven_regular_edge
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → Fin n → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((1 : ℝ) / 2) := by
  obtain ⟨d, k, H, r, c₀, C, hcase, hH, hr, hc₀, hC, hbound⟩ :=
    main_theorem_seven_regular_frontier perron algebraic puiseux ift rootArgument hn S a hS hirr
      m hupper heq τ i hfront hτ
  have hcoefficient := frontier_coefficient_iff_support_topology normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ d
  have hσ := hcoefficient.1.mpr hedge
  have hk : k = 2 := by
    rcases hcase with ⟨hk, _⟩ | ⟨_, hz, _⟩
    · exact hk
    · exact False.elim (hσ hz)
  refine ⟨H, r, c₀, C, hH, hr, hc₀, hC, ?_⟩
  simpa only [hk, Nat.cast_ofNat, show (1 - (1 : ℝ) / 2) = 1 / 2 by norm_num] using hbound

/-- The two-thirds denominator at a genuine two-sided regular cusp. -/
theorem main_theorem_seven_regular_cusp
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → Fin n → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ ((2 : ℝ) / 3) := by
  obtain ⟨d, k, H, r, c₀, C, hcase, hH, hr, hc₀, hC, hbound⟩ :=
    main_theorem_seven_regular_frontier perron algebraic puiseux ift rootArgument hn S a hS hirr
      m hupper heq τ i hfront hτ
  have hcoefficient := frontier_coefficient_iff_support_topology normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ d
  have hσ := hcoefficient.2.mpr hcusp
  have hk : k = 3 := by
    rcases hcase with ⟨_, hn⟩ | ⟨hk, _, _⟩
    · exact False.elim (hn hσ)
    · exact hk
  refine ⟨H, r, c₀, C, hH, hr, hc₀, hC, ?_⟩
  simpa only [hk, Nat.cast_ofNat, show (1 - (1 : ℝ) / 3) = 2 / 3 by norm_num] using hbound

end Model
end NonSymmetricDyson.Full.Nonlinear
