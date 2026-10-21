import Dyson.Paper.FoundationsPaths
import Dyson.Full.BoundaryBounds

/-! The M3 proof with the manuscript's shortest-path positivity step.
The remaining estimates are the same actual Dyson and Stieltjes calculations
as the checked analytic backend. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Set MeasureTheory
namespace NonSymmetricDyson.Paper.RegularityBounds
open Full Full.Boundary Full.ExternalAlgebraic Full.Foundations Full.StieltjesTails
open Manuscript.StripComparability BasicEstimates
theorem path_strip_comparability
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ),
      0 < z.im → |z.re| ≤ T → IsUpperSolution m → IsDysonSolution S a z m →
      (∀ i, L / (1 + ‖z‖) ≤ ‖m i‖) →
        ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  let q : ℝ := (L / (T + 2)) ^ 2
  have hq : 0 < q := sq_pos_of_pos (div_pos hL (by linarith))
  obtain ⟨C₀, hC₀, hsmall⟩ := FoundationsPaths.imaginary_parts_comparable hn S hS hirr q hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let C : ℝ := min C₀ (q / n)
  have hC : 0 < C := lt_min hC₀ (div_pos hq hnR)
  refine ⟨C, hC, ?_⟩
  intro a z m hz hRe hm hsol hlower i
  have hznorm : ‖z‖ ≤ T + z.im := by
    have hb := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at hb
    linarith
  have htotalpos : 0 ≤ ∑ j, (m j).im :=
    Finset.sum_nonneg (fun j _ => (hm j).le)
  by_cases hheight : z.im ≤ 1
  · have hmod : ∀ j, q ≤ Complex.normSq (m j) := by
      intro j
      have hl := small_height_modulus_lower_bound T L hT z hznorm hheight
        (m j) (hlower j)
      have hd : 0 < L / (T + 2) := div_pos hL (by linarith)
      rw [Complex.normSq_eq_norm_sq]
      dsimp only [q]
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hd.le (norm_nonneg (m j)))]
    exact (mul_le_mul_of_nonneg_right (min_le_left C₀ (q / n)) htotalpos).trans
      (hsmall a z m hz.le hm hsol hmod i)
  · have hheight' : 1 ≤ z.im := le_of_lt (lt_of_not_ge hheight)
    have hlow : q ≤ z.im * (m i).im :=
      large_height_imaginary_part_lower_bound S hS a T L hT hL z hznorm
        hheight' m hm hsol hlower i
    have htotal := height_times_total_imaginary_part_le_dimension S hS a z hz m hm hsol
    have hCn : C * (n : ℝ) ≤ q :=
      (le_div_iff₀ hnR).mp (min_le_right C₀ (q / n))
    have hupper := (mul_le_mul_of_nonneg_left htotal hC.le).trans hCn
    have hfin : (C * (∑ j, (m j).im)) * z.im ≤ (m i).im * z.im := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hz).mp (by simpa only [mul_comm] using hfin)

/-- The imaginary-part comparison for actual Dyson solutions follows from
a uniform component norm bound. No imaginary-part comparison or modulus
lower bound is assumed here: the latter is proved from the Dyson equation.
The constant depends only on `S`, `a`, `M`, `T`, and the dimension. -/
theorem path_strip_comparability_of_uniform_bound
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a : Fin n → ℝ) (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : Fin n → ℂ),
      0 < z.im → |z.re| ≤ T → IsUpperSolution m → IsDysonSolution S a z m →
      (∀ i, ‖m i‖ ≤ M) →
        ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  let L := NonSymmetricDyson.ComponentBounds.uniformLowerConstant S a M
  have hL : 0 < L :=
    NonSymmetricDyson.ComponentBounds.uniformLowerConstant_pos hS hM
  obtain ⟨C, hC, hcomp⟩ := path_strip_comparability
    hn S hS hirr T L hT hL
  refine ⟨C, hC, ?_⟩
  intro z m hz hRe hm hsol hbound i
  exact hcomp a z m hz hRe hm hsol
    (fun j => NonSymmetricDyson.ComponentBounds.common_scaled_lower_bound
      hS hm hsol hM hbound j) i

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
    path_strip_comparability_of_uniform_bound
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
      exact (hall (Full.Boundary.vertical z.re η) (by simpa [Full.Boundary.vertical] using hz.1) (by simpa using hη)).2 i j
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
      exact (hall (Full.Boundary.vertical z.re η) (by simpa [Full.Boundary.vertical] using hz.1) (by simpa using hη)).1
  · intro i j
    refine ⟨hpairs i j, ?_⟩
    have h := mul_le_mul_of_nonneg_left (hpairs j i) (inv_nonneg.mpr hβ.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul] using h

end NonSymmetricDyson.Paper.RegularityBounds
