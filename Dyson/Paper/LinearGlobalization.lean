import Dyson.Full.MainLinearSingular

/-! The revised cusp theorem needs only an upper estimate. This globalization
uses its local upper estimate, the manuscript's middle-height estimate, and
the high-height contraction; it assumes no lower cusp estimate. -/
noncomputable section
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.LinearGlobalization
open Full
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem upper_full_height_globalization
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (τ α r C₀ : ℝ) (hr : 0 < r) (hC₀ : 0 < C₀)
    (hlocal : ∀ (z : ℂ) (hz : 0 < z.im), ‖z-(τ:ℂ)‖ < r →
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ≤ C₀ / ‖z-(τ:ℂ)‖^α) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
          (hupper z hz) (hsol z hz)‖ ≤ C * max 1 (1 / ‖z-(τ:ℂ)‖^α) := by
  let δ : ℝ := min r 1 / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : 2*δ < r := by
    have hmin := min_le_left r 1
    dsimp [δ]
    linarith [lt_min hr zero_lt_one]
  let R : ℝ := ‖fun i => ∑ j, S i j‖
  have hR : 0 ≤ R := norm_nonneg _
  have hrow (i : ι) : ∑ j, S i j ≤ R :=
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H : ℝ := 1+2*R+δ
  have hδH : δ ≤ H := by dsimp [H]; linarith
  obtain ⟨A,hA,hmid⟩ := Linear.middle_rectangle_lower_norm_bound S a (|τ|+δ) δ H hS
    (by positivity) hδ hδH
  let d : ℝ := Real.sqrt (Fintype.card ι)
  let C : ℝ := max C₀ (d*max A 2)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro z hz hE
  by_cases hnear : z.im < δ
  · have hnormupper : ‖z-(τ:ℂ)‖ ≤ |z.re-τ|+z.im := by
      simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z-(τ:ℂ))
    have hzr : ‖z-(τ:ℂ)‖ < r := lt_of_le_of_lt hnormupper (by linarith)
    calc
      _ ≤ C₀/‖z-(τ:ℂ)‖^α := hlocal z hz hzr
      _ = C₀*(1/‖z-(τ:ℂ)‖^α) := by ring
      _ ≤ C*(1/‖z-(τ:ℂ)‖^α) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C*max 1 (1/‖z-(τ:ℂ)‖^α) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le
  · have hη : δ ≤ z.im := le_of_not_gt hnear
    have hbound : ∀ u, ‖u‖ ≤ max A 2 * ‖InteriorStability.stabilityOperator S (m z) u‖ := by
      intro u
      by_cases hhigh : z.im ≤ H
      · have hreal : |z.re| ≤ |τ|+δ := by
          have hh := abs_add_le (z.re-τ) τ
          have hid : z.re-τ+τ = z.re := by ring
          rw [hid] at hh
          linarith
        exact (hmid z (m z) hreal hη hhigh (hupper z hz) (hsol z hz) u).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · have hrows : ∀ i, 2*∑ j, S i j ≤ z.im^2 := by
          intro i
          have hHsq : 2*R ≤ H^2 := by dsimp [H]; nlinarith
          nlinarith [hrow i, lt_of_not_ge hhigh]
        exact (Linear.high_height_lower_norm_bound S a z (m z) hS hz
          (hupper z hz) (hsol z hz) hrows u).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hu := EuclideanInverse.stability_inverse_upper S a z (m z) hS hz
      (hupper z hz) (hsol z hz) (max A 2) (by positivity) hbound
    exact (hu.trans (le_max_right C₀ _)).trans
      (le_mul_of_one_le_right hC.le (le_max_left _ _))

theorem upper_full_height_of_eventual
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (τ α C₀ : ℝ) (hα : 0 < α) (hC₀ : 0 < C₀)
    (hlocal : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (τ : ℂ), ∀ hz : 0 < z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ≤ C₀ / ‖z-(τ:ℂ)‖^α) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
          (hupper z hz) (hsol z hz)‖ ≤ C * max 1 (1/(|z.re-τ|+z.im)^α) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hlocal
  obtain ⟨δ,C,hδ,hC,hbound⟩ := upper_full_height_globalization S a m hS hupper hsol
    τ α r C₀ hr hC₀ (fun z hz hzr =>
      hball ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hzr, hz⟩ hz)
  refine ⟨δ,C*(2:ℝ)^α,hδ,by positivity,?_⟩
  intro z hz hE
  obtain ⟨_,hwhi⟩ := MainLinearSingular.distance_weight_comparison τ α hα z hz
  exact (hbound z hz hE).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwhi hC.le)

end NonSymmetricDyson.Paper.LinearGlobalization
