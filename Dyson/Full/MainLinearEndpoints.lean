import Dyson.Full.MainLinearFrontier
import Dyson.Full.SingularityTopology

/-! The literal edge and cusp clauses of M6. Point type is read from the
actual regular support; no analytic degree or inverse bound is assumed. -/
noncomputable section
open scoped Topology
namespace NonSymmetricDyson.Full.MainLinearSingular
open Singularities ExternalAlgebraic SingularLinear

theorem main_theorem_six_edge
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
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) := by
  obtain ⟨nf⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hd := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a
    hS hirr m hupper heq τ i hfront hτ nf).1.mpr hkind
  have hb := regular_frontier_normal_form_full_strip perron hn algebraic puiseux S a
    hS hirr m hupper heq τ i hfront hτ nf
  simpa [hd, inverseExponent] using hb

theorem main_theorem_six_cusp
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
    (hτ : τ ∉ Boundary.singularUnion m)
    (hkind : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  obtain ⟨nf⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hd := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a
    hS hirr m hupper heq τ i hfront hτ nf).2.mpr hkind
  have hb := regular_frontier_normal_form_full_strip perron hn algebraic puiseux S a
    hS hirr m hupper heq τ i hfront hτ nf
  simpa [hd, inverseExponent] using hb

end NonSymmetricDyson.Full.MainLinearSingular
