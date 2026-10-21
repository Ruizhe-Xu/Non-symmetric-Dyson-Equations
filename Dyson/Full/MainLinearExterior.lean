import Dyson.Full.OffSupport
import Dyson.Full.EuclideanInverse

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace NonSymmetricDyson.Full.OffSupport
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- M6, off-support clause in the manuscript's ordinary Euclidean operator
norm, simultaneously for every real energy and every positive height. -/
theorem main_theorem_six_exterior
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (hS : ∀ i j, 0 ≤ S i j)
    (A R Sigma ε : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hSigma : 0 ≤ Sigma) (hε : 0 < ε)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hsupport : ∀ i, ∀ᵐ t ∂μ i, |t| ≤ Sigma)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ E η : ℝ, ∀ hη : 0 < η,
      (∀ i, ∀ᵐ t ∂μ i, ε ≤ |t-E|) →
      let m := fun i => Poisson.stieltjes (μ i) (Poisson.point E η)
      let hz : 0 < (Poisson.point E η).im := by simpa [Poisson.point] using hη
      c ≤ ‖EuclideanInverse.stabilityInverse S a (Poisson.point E η) m hS hz
        (hupper _ hz) (hsol _ hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a (Poisson.point E η) m hS hz
        (hupper _ hz) (hsol _ hz)‖ ≤ C := by
  letI : ∀ i, IsProbabilityMeasure (μ i) := hμ
  obtain ⟨C, hC, hbound⟩ := exterior_uniform_bound S a μ hμ hS A R Sigma ε
    hA hR hSigma hε ha hrow hsupport hupper hsol
  let d : ℝ := Real.sqrt (Fintype.card ι)
  have hd : 0 < d := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  let c : ℝ := (1 / (1 + (ε⁻¹)^2*R)) / d
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, d*C, hc, mul_pos hd hC, ?_⟩
  intro E η hη hgap
  dsimp only
  let m := fun i => Poisson.stieltjes (μ i) (Poisson.point E η)
  have hz : 0 < (Poisson.point E η).im := by simpa [Poisson.point] using hη
  have hmod : ∀ i, ‖m i‖ ≤ ε⁻¹ := fun i => Poisson.stieltjes_norm_of_gap (μ i) hε (hgap i)
  constructor
  · have hl := Linear.inverse_norm_lower_bound S a (Poisson.point E η) m hS hz
      (hupper _ hz) (hsol _ hz) (ε⁻¹) R (by positivity) hR hmod hrow
    have he := EuclideanInverse.conjugate_norm_lower
      (InteriorStability.stabilityContinuousEquiv hS hz (hupper _ hz) (hsol _ hz)).symm.toContinuousLinearMap
    change 1 / (1 + (ε⁻¹)^2*R) ≤ _ at hl
    apply (div_le_iff₀ hd).mpr
    exact (hl.trans he).trans_eq (mul_comm _ _)
  · exact EuclideanInverse.stability_inverse_upper S a (Poisson.point E η) m hS hz
      (hupper _ hz) (hsol _ hz) C hC.le (hbound E η hη.le hgap)

end NonSymmetricDyson.Full.OffSupport
