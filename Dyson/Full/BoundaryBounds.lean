import Dyson.Full.MainBoundary
import Dyson.Full.StieltjesTails
import Dyson.ComponentBounds

/-! Component bounds on arbitrary closed vertical strips, including
unbounded real intervals. The far-region estimates are derived from the
actual probability Stieltjes integral and its compact support. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic Foundations StieltjesTails Poisson

theorem stieltjes_norm_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {z : ℂ} {σ : ℝ} (hσ : 0 ≤ σ) (hz : 2 * σ + 1 ≤ ‖z‖)
    (hs : ∀ᵐ t : ℝ ∂μ, |t| ≤ σ) :
    ‖Poisson.stieltjes μ z‖ ≤ 2 / (1 + ‖z‖) := by
  have hd : 0 < ‖z‖ - σ := by linarith
  have hnorm : ‖Poisson.stieltjes μ z‖ ≤ (‖z‖ - σ)⁻¹ := by
    simpa [Poisson.stieltjes] using norm_integral_le_of_norm_le_const
      (hs.mono fun t ht => resolvent_norm_of_complex_gap hd (norm_denominator_bounds ht).1)
  apply hnorm.trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hd (by positivity : 0 < 1 + ‖z‖)).mpr
  linarith

theorem imaginary_tail_ratio (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {z : ℂ} {σ : ℝ} (hσ : 0 ≤ σ) (hz : 2 * σ + 1 ≤ ‖z‖) (him : 0 < z.im)
    (hμ : ∀ᵐ t : ℝ ∂μ, |t| ≤ σ) (hν : ∀ᵐ t : ℝ ∂ν, |t| ≤ σ) :
    (Poisson.stieltjes μ z).im ≤ 9 * (Poisson.stieltjes ν z).im := by
  have hzrep : Poisson.point z.re z.im = z := by
    exact Complex.ext (by simp [Poisson.point]) (by simp [Poisson.point])
  have hσz : σ < ‖Poisson.point z.re z.im‖ := by rw [hzrep]; linarith
  have hlo := (imaginary_tail_bounds ν hσ him hσz hν).1
  have hhi := (imaginary_tail_bounds μ hσ him hσz hμ).2
  rw [hzrep] at hlo hhi
  have hd : 0 < ‖z‖ - σ := by linarith
  have hp : 0 < ‖z‖ + σ := by linarith
  have hratio : z.im / (‖z‖ - σ)^2 ≤ 9 * (z.im / (‖z‖ + σ)^2) := by
    have hsquare : (‖z‖ + σ)^2 ≤ 9 * (‖z‖ - σ)^2 := by nlinarith
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsquare him.le]
  exact hhi.trans (hratio.trans (mul_le_mul_of_nonneg_left hlo (by norm_num)))

theorem family_interior_global_bounds {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hσ : 0 ≤ σ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (I : Set ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M) :
    ∃ c C β : ℝ, 0 < c ∧ 0 < C ∧ 0 < β ∧
      ∀ z : ℂ, z.re ∈ I → 0 < z.im →
        (∀ i, c / (1 + ‖z‖) ≤ ‖m z i‖ ∧ ‖m z i‖ ≤ C / (1 + ‖z‖)) ∧
        (∀ i j, β * (m z j).im ≤ (m z i).im) := by
  let K : ℝ := 2 * σ + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨b, hb, hcomp⟩ :=
    Manuscript.StripComparability.dyson_imaginary_parts_comparable_of_uniform_bound
      hn S hS hirr a M K hM hK
  let C : ℝ := max (M * (1 + K)) 2
  let β : ℝ := min b (1 / 9)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  have hβ : 0 < β := lt_min hb (by norm_num)
  refine ⟨ComponentBounds.uniformLowerConstant S a M, C, β,
    ComponentBounds.uniformLowerConstant_pos hS hM, hC, hβ, ?_⟩
  intro z hzI hz
  have hm := hupper z hz
  have hsol := heq z hz
  have hmod := hbound z hzI hz
  have hst (i : Fin n) : m z i = Poisson.stieltjes (μ i) z := hrep i z hz
  have hs (i : Fin n) : ∀ᵐ t : ℝ ∂μ i, |t| ≤ σ := ae_abs_le_of_support (μ i) (hsupport i)
  constructor
  · intro i
    refine ⟨ComponentBounds.common_scaled_lower_bound hS hm hsol hM hmod i, ?_⟩
    by_cases hsmall : ‖z‖ ≤ K
    · apply (le_div_iff₀ (by positivity : 0 < 1 + ‖z‖)).mpr
      calc
        ‖m z i‖ * (1 + ‖z‖) ≤ M * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (hmod i) (by positivity)
        _ ≤ M * (1 + K) := mul_le_mul_of_nonneg_left (by linarith) hM
        _ ≤ C := le_max_left _ _
    · letI := hμ i
      rw [hst i]
      exact (stieltjes_norm_tail (μ i) hσ (le_of_lt (lt_of_not_ge hsmall)) (hs i)).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))
  · intro i j
    by_cases hsmall : ‖z‖ ≤ K
    · have hreal : |z.re| ≤ K := (Complex.abs_re_le_norm z).trans hsmall
      have hbnd := hcomp z (m z) hz hreal hm hsol hmod i
      have hyj : (m z j).im ≤ ∑ k, (m z k).im :=
        Finset.single_le_sum (fun k _ => (hm k).le) (Finset.mem_univ j)
      calc
        β * (m z j).im ≤ b * (m z j).im :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (hm j).le
        _ ≤ b * (∑ k, (m z k).im) := mul_le_mul_of_nonneg_left hyj hb.le
        _ ≤ _ := hbnd
    · letI := hμ i
      letI := hμ j
      have hratio := imaginary_tail_ratio (μ j) (μ i) hσ
        (le_of_lt (lt_of_not_ge hsmall)) hz (hs j) (hs i)
      rw [← hst j, ← hst i] at hratio
      have hβle : β ≤ 1 / 9 := min_le_right _ _
      have hstep := mul_le_mul_of_nonneg_right hβle (hm j).le
      nlinarith

end NonSymmetricDyson.Full.Boundary

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic Foundations

theorem strip_disjoint_singular {ι : Type*} [Fintype ι]
    (m : ℂ → ι → ℂ) (I : Set ℝ) (M : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M)
    (τ : ℝ) (hτ : τ ∈ I) : τ ∉ singularUnion m := by
  intro hs
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
  apply not_singular_of_bounded (f := fun z => m z i) (M := M) ?_ hi
  intro η hη
  exact hbound (vertical τ η) (by simpa [vertical] using hτ) (by simpa using hη) i

theorem family_extension_agrees {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (z : ℂ) (hz : z ∈ upper) : boundaryVector m z = m z := by
  funext i
  exact extendFrom_extends
    (family_coordinate_analytic S a hS m hupper heq i).continuousOn z hz

/-- M3: the complete component comparison on the closed strip. The
arbitrary set I in this statement includes every nonempty closed interval,
bounded or unbounded. The extension and its nonzero boundary coordinates
were derived from the interior equation and bound. -/
theorem main_theorem_three {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hσ : 0 ≤ σ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (I : Set ℝ) (Φ : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ Φ) :
    ContinuousOn (boundaryVector m) (closedStrip I) ∧
    ∃ c C β : ℝ, 0 < c ∧ 0 < C ∧ 0 < β ∧
      ∀ z ∈ closedStrip I,
        (∀ i, c / (1 + ‖z‖) ≤ ‖boundaryVector m z i‖ ∧
          ‖boundaryVector m z i‖ ≤ C / (1 + ‖z‖)) ∧
        (∀ i j, β * (boundaryVector m z j).im ≤ (boundaryVector m z i).im ∧
          (boundaryVector m z i).im ≤ β⁻¹ * (boundaryVector m z j).im) := by
  have hcont := family_closedStrip_continuous algebraic puiseux S a hS m hupper heq I Φ hbound
  let M : ℝ := max 0 Φ
  have hM : 0 ≤ M := le_max_left _ _
  have hboundM : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M :=
    fun z hzI hz i => (hbound z hzI hz i).trans (le_max_right _ _)
  obtain ⟨c, C, β, hc, hC, hβ, hall⟩ := family_interior_global_bounds hn S a hS hirr
    m hupper heq μ hμ hrep σ hσ hsupport I M hM hboundM
  refine ⟨hcont, c, C, β, hc, hC, hβ, ?_⟩
  intro z hz
  have hpairs : ∀ i j, β * (boundaryVector m z j).im ≤ (boundaryVector m z i).im := by
    by_cases hzpos : 0 < z.im
    · rw [family_extension_agrees S a hS m hupper heq z hzpos]
      exact (hall z hz.1 hzpos).2
    · have hzero : z.im = 0 := le_antisymm (le_of_not_gt hzpos) hz.2
      have heqz : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
      have hnot := strip_disjoint_singular m I Φ hbound z.re hz.1
      have hlim := family_boundary_limits algebraic puiseux S a hS m hupper heq z.re hnot
      rw [heqz] at hlim
      intro i j
      have hi := Complex.continuous_im.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hlim i)
      have hj := Complex.continuous_im.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hlim j)
      apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hj) hi
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact (hall (vertical z.re η) (by simpa [vertical] using hz.1) (by simpa using hη)).2 i j
  constructor
  · by_cases hzpos : 0 < z.im
    · rw [family_extension_agrees S a hS m hupper heq z hzpos]
      exact (hall z hz.1 hzpos).1
    · have hzero : z.im = 0 := le_antisymm (le_of_not_gt hzpos) hz.2
      have heqz : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
      have hnot := strip_disjoint_singular m I Φ hbound z.re hz.1
      have hlim := family_boundary_limits algebraic puiseux S a hS m hupper heq z.re hnot
      have hzlim := vertical_tendsto z.re
      rw [heqz] at hlim hzlim
      apply scaled_bounds_limit hlim hzlim
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact (hall (vertical z.re η) (by simpa [vertical] using hz.1) (by simpa using hη)).1
  · intro i j
    refine ⟨hpairs i j, ?_⟩
    have h := mul_le_mul_of_nonneg_left (hpairs j i) (inv_nonneg.mpr hβ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul] using h

end NonSymmetricDyson.Full.Boundary
