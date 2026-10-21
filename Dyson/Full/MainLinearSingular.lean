import Dyson.Full.EuclideanInverse
import Dyson.Full.PowerGluing

/-! Globalization of the actual local edge/cusp inverse estimate through every
positive height. Intermediate heights use the explicit Dyson estimate and
large heights use the row contraction, so no compact boundary stability
assumption is needed. -/
noncomputable section
open scoped BigOperators Topology
namespace NonSymmetricDyson.Full.MainLinearSingular
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A local fractional inverse rate extends to an entire vertical strip about
its real singularity. Both sides concern the Euclidean operator norm of the
actual Dyson inverse. -/
theorem singular_full_height_globalization
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (τ α r c₀ C₀ : ℝ) (hα : 0 < α) (hr : 0 < r)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hlocal : ∀ (z : ℂ) (hz : 0 < z.im), ‖z-(τ:ℂ)‖ < r →
      c₀ / ‖z-(τ:ℂ)‖^α ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ≤ C₀ / ‖z-(τ:ℂ)‖^α) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1 / ‖z-(τ:ℂ)‖^α) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ≤
          C * max 1 (1 / ‖z-(τ:ℂ)‖^α) := by
  let δ : ℝ := min r 1 / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : 2*δ < r := by
    have hmin := min_le_left r 1
    dsimp [δ]
    linarith [lt_min hr zero_lt_one]
  have hδ1 : 2*δ ≤ 1 := by dsimp [δ]; linarith [min_le_right r 1]
  let R : ℝ := ‖fun i => ∑ j, S i j‖
  have hR : 0 ≤ R := norm_nonneg _
  have hrow (i : ι) : ∑ j, S i j ≤ R :=
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H : ℝ := 1+2*R+δ
  have hH : 0 < H := by dsimp [H]; positivity
  have hδH : δ ≤ H := by dsimp [H]; linarith
  obtain ⟨A,hA,hmid⟩ := Linear.middle_rectangle_lower_norm_bound S a (|τ|+δ) δ H hS
    (by positivity) hδ hδH
  let d : ℝ := Real.sqrt (Fintype.card ι)
  have hd : 0 < d := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  let b : ℝ := (1/(1+(δ⁻¹)^2*R))/d
  have hb : 0 < b := by dsimp [b]; positivity
  let W : ℝ := max 1 (1/δ^α)
  have hW : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let c : ℝ := min c₀ (b/W)
  let C : ℝ := max C₀ (d*max A 2)
  have hc : 0 < c := lt_min hc₀ (div_pos hb hW)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨δ,c,C,hδ,hc,hC,?_⟩
  intro z hz hE
  let N : ℝ := ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
    (hupper z hz) (hsol z hz)‖
  have hzn : 0 < ‖z-(τ:ℂ)‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    exact (ne_of_gt hz) hh
  have hzp : 0 < ‖z-(τ:ℂ)‖^α := Real.rpow_pos_of_pos hzn _
  have hheight : z.im ≤ ‖z-(τ:ℂ)‖ := by
    simpa using Complex.im_le_norm (z-(τ:ℂ))
  have hnormupper : ‖z-(τ:ℂ)‖ ≤ |z.re-τ|+z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z-(τ:ℂ))
  by_cases hnear : z.im < δ
  · have hzr : ‖z-(τ:ℂ)‖ < r := lt_of_le_of_lt hnormupper (by linarith)
    have hz1 : ‖z-(τ:ℂ)‖ ≤ 1 := hnormupper.trans (by linarith)
    have hpow1 : ‖z-(τ:ℂ)‖^α ≤ 1 := Real.rpow_le_one hzn.le hz1 hα.le
    have hweight : max 1 (1 / ‖z-(τ:ℂ)‖^α) = 1 / ‖z-(τ:ℂ)‖^α := by
      apply max_eq_right
      exact (one_le_div hzp).mpr hpow1
    rw [hweight]
    constructor
    · calc
        c*(1/‖z-(τ:ℂ)‖^α) ≤ c₀*(1/‖z-(τ:ℂ)‖^α) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = c₀/‖z-(τ:ℂ)‖^α := by ring
        _ ≤ N := (hlocal z hz hzr).1
    · calc
        N ≤ C₀/‖z-(τ:ℂ)‖^α := (hlocal z hz hzr).2
        _ = C₀*(1/‖z-(τ:ℂ)‖^α) := by ring
        _ ≤ C*(1/‖z-(τ:ℂ)‖^α) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hη : δ ≤ z.im := le_of_not_gt hnear
    have hmod (i : ι) : ‖m z i‖ ≤ δ⁻¹ :=
      (BasicEstimates.rough_bound hS hz (hupper z hz) (hsol z hz) i).trans
        (inv_anti₀ hδ hη)
    have hbN : b ≤ N := by
      have hl := Linear.inverse_norm_lower_bound S a z (m z) hS hz (hupper z hz) (hsol z hz)
        δ⁻¹ R (by positivity) hR hmod hrow
      have he := EuclideanInverse.conjugate_norm_lower
        (InteriorStability.stabilityContinuousEquiv hS hz (hupper z hz) (hsol z hz)).symm.toContinuousLinearMap
      exact (div_le_iff₀ hd).mpr ((hl.trans he).trans_eq (mul_comm _ _))
    have hweight : max 1 (1 / ‖z-(τ:ℂ)‖^α) ≤ W := by
      apply max_le_max le_rfl
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ _)
        (Real.rpow_le_rpow hδ.le (hη.trans hheight) hα.le)
    constructor
    · have hcb : c*W ≤ b := (le_div_iff₀ hW).mp (min_le_right c₀ (b/W))
      exact ((mul_le_mul_of_nonneg_left hweight hc.le).trans hcb).trans hbN
    · have hbound : ∀ u, ‖u‖ ≤ max A 2 * ‖InteriorStability.stabilityOperator S (m z) u‖ := by
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

/-- The Euclidean distance to the real singularity and κ+η give equivalent
fractional weights, with an explicit factor 2^α. -/
theorem distance_weight_comparison (τ α : ℝ) (hα : 0 < α)
    (z : ℂ) (hz : 0 < z.im) :
    max 1 (1/(|z.re-τ|+z.im)^α) ≤ max 1 (1/‖z-(τ:ℂ)‖^α) ∧
    max 1 (1/‖z-(τ:ℂ)‖^α) ≤ (2:ℝ)^α * max 1 (1/(|z.re-τ|+z.im)^α) := by
  have hn : 0 < ‖z-(τ:ℂ)‖ := by
    have hh : z.im ≤ ‖z-(τ:ℂ)‖ := by simpa using Complex.im_le_norm (z-(τ:ℂ))
    exact hz.trans_le hh
  have hq : 0 < |z.re-τ|+z.im := add_pos_of_nonneg_of_pos (abs_nonneg _) hz
  have hlo : ‖z-(τ:ℂ)‖ ≤ |z.re-τ|+z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z-(τ:ℂ))
  have hhi : |z.re-τ|+z.im ≤ 2*‖z-(τ:ℂ)‖ := by
    have hr : |z.re-τ| ≤ ‖z-(τ:ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (z-(τ:ℂ))
    have hi : z.im ≤ ‖z-(τ:ℂ)‖ := by simpa using Complex.im_le_norm (z-(τ:ℂ))
    linarith
  have hnp : 0 < ‖z-(τ:ℂ)‖^α := Real.rpow_pos_of_pos hn _
  have hqp : 0 < (|z.re-τ|+z.im)^α := Real.rpow_pos_of_pos hq _
  have htwo : 1 ≤ (2:ℝ)^α := Real.one_le_rpow (by norm_num) hα.le
  constructor
  · exact max_le_max le_rfl (one_div_le_one_div_of_le hnp
      (Real.rpow_le_rpow hn.le hlo hα.le))
  · have hp : (|z.re-τ|+z.im)^α ≤ (2:ℝ)^α * ‖z-(τ:ℂ)‖^α := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn.le]
      exact Real.rpow_le_rpow hq.le hhi hα.le
    have hdiv : 1/‖z-(τ:ℂ)‖^α ≤ (2:ℝ)^α * (1/(|z.re-τ|+z.im)^α) := by
      rw [mul_one_div]
      apply (div_le_div_iff₀ hnp hqp).mpr
      simpa using hp
    apply max_le
    · exact htwo.trans (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
    · exact hdiv.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))

/-- Manuscript κ+η version of the full-height edge/cusp strip estimate. -/
theorem singular_full_height_kappa_eta
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (τ α r c₀ C₀ : ℝ) (hα : 0 < α) (hr : 0 < r)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hlocal : ∀ (z : ℂ) (hz : 0 < z.im), ‖z-(τ:ℂ)‖ < r →
      c₀ / ‖z-(τ:ℂ)‖^α ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ≤ C₀ / ‖z-(τ:ℂ)‖^α) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^α) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^α) := by
  obtain ⟨δ,c,C,hδ,hc,hC,hbound⟩ := singular_full_height_globalization S a m hS hupper hsol
    τ α r c₀ C₀ hα hr hc₀ hC₀ hlocal
  refine ⟨δ,c,C*(2:ℝ)^α,hδ,hc,by positivity,?_⟩
  intro z hz hE
  obtain ⟨hwlo,hwhi⟩ := distance_weight_comparison τ α hα z hz
  constructor
  · exact (mul_le_mul_of_nonneg_left hwlo hc.le).trans (hbound z hz hE).1
  · exact (hbound z hz hE).2.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwhi hC.le)

/-- Filter-form local estimates from a physical normal form feed directly
into the all-height κ+η theorem. -/
theorem singular_full_height_of_eventual
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (τ α c₀ C₀ : ℝ) (hα : 0 < α) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hlocal : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (τ : ℂ), ∀ hz : 0 < z.im,
      c₀ / ‖z-(τ:ℂ)‖^α ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z hz) (hsol z hz)‖ ≤ C₀ / ‖z-(τ:ℂ)‖^α) :
    ∃ δ c C : ℝ, 0 < δ ∧ 0 < c ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        c * max 1 (1/(|z.re-τ|+z.im)^α) ≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (hsol z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^α) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hlocal
  apply singular_full_height_kappa_eta S a m hS hupper hsol τ α r c₀ C₀ hα hr hc₀ hC₀
  intro z hz hzr
  exact hball ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hzr, hz⟩ hz

end NonSymmetricDyson.Full.MainLinearSingular
