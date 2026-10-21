import Dyson.Full.MainSingularities
import Dyson.Full.BoundaryLocalLimits

noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- Two square roots in the same closed upper quadrant satisfy the exact
power difference estimate. This is the elementary root Hölder inequality. -/
theorem quadrant_square_difference (c : ℝ) (hc : c ≠ 0) (s t : ℂ)
    (hs : 0 ≤ s.im) (ht : 0 ≤ t.im) (hsc : 0 ≤ c * s.re) (htc : 0 ≤ c * t.re) :
    ‖s - t‖ ^ 2 ≤ ‖s ^ 2 - t ^ 2‖ := by
  have hre : 0 ≤ s.re * t.re := by
    have hp := mul_nonneg hsc htc
    have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith
  have hle : ‖s - t‖ ≤ ‖s + t‖ := by
    have h₁ := Complex.sq_norm (s-t)
    have h₂ := Complex.sq_norm (s+t)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im] at h₁ h₂
    nlinarith [mul_nonneg hs ht, norm_nonneg (s-t), norm_nonneg (s+t)]
  calc
    ‖s-t‖ ^ 2 ≤ ‖s-t‖ * ‖s+t‖ := by nlinarith [norm_nonneg (s-t)]
    _ = ‖(s-t)*(s+t)‖ := (norm_mul _ _).symm
    _ = ‖s^2-t^2‖ := by congr 1; ring

/-- Two roots in the physical cubic sector satisfy a quantitative cubic
power difference estimate. The proof uses only real and complex algebra. -/
theorem central_cube_difference (s t : ℂ)
    (hs : 0 ≤ s.im) (ht : 0 ≤ t.im)
    (hsc : 3 * s.re ^ 2 ≤ s.im ^ 2) (htc : 3 * t.re ^ 2 ≤ t.im ^ 2) :
    ‖s - t‖ ^ 3 ≤ 4 * ‖s ^ 3 - t ^ 3‖ := by
  have hcross : s.re * t.re ≤ s.im * t.im := by
    have hsr : |s.re| ≤ s.im := by nlinarith [sq_abs s.re, abs_nonneg s.re]
    have htr : |t.re| ≤ t.im := by nlinarith [sq_abs t.re, abs_nonneg t.re]
    calc
      s.re*t.re ≤ |s.re*t.re| := le_abs_self _
      _ = |s.re| * |t.re| := abs_mul _ _
      _ ≤ s.im*t.im := mul_le_mul hsr htr (abs_nonneg _) hs
  let A := s ^ 2 + s * t + t ^ 2
  have hreal : (‖s‖ ^ 2 + ‖t‖ ^ 2) / 2 ≤ -A.re := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply]
    dsimp [A]
    simp only [Complex.add_re, Complex.mul_re, pow_two]
    nlinarith
  have hfactor : (‖s‖ ^ 2 + ‖t‖ ^ 2) / 2 ≤ ‖A‖ := hreal.trans
    ((neg_le_abs A.re).trans (Complex.abs_re_le_norm A))
  have hdiff : ‖s-t‖ ^ 2 ≤ 2 * (‖s‖ ^ 2 + ‖t‖ ^ 2) := by
    have hn := norm_sub_le s t
    nlinarith [sq_nonneg (‖s‖-‖t‖), norm_nonneg s, norm_nonneg t, norm_nonneg (s-t)]
  have hbound : ‖s-t‖ ^ 2 ≤ 4 * ‖A‖ := by linarith
  calc
    ‖s-t‖ ^ 3 ≤ 4 * (‖s-t‖ * ‖A‖) := by nlinarith [mul_le_mul_of_nonneg_left hbound (norm_nonneg (s-t))]
    _ = 4 * ‖(s-t)*A‖ := by rw [norm_mul]
    _ = 4 * ‖s^3-t^3‖ := by congr 2; dsimp [A]; ring

/-- Taking a real positive kth root converts a power estimate to Hölder
form; all constants remain explicit. -/
theorem root_bound_of_power_bound (a b C : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hk : 0 < k)
    (h : a ^ k ≤ C * b) : a ≤ C ^ ((k : ℝ)⁻¹) * b ^ ((k : ℝ)⁻¹) := by
  have he := Real.rpow_le_rpow (pow_nonneg ha k) h (by positivity : 0 ≤ (k : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast ha hk.ne', Real.mul_rpow hC hb] at he

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual physical monomial chart gives the full two-point 1/3-Hölder
estimate in an upper half-neighborhood. No root-continuity estimate is added
as an external premise: the two root power inequalities above prove it. -/
theorem PhysicalNormalForm.upper_one_third_holder
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ} {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ z ∈ ExternalAlgebraic.upper, ∀ w ∈ ExternalAlgebraic.upper,
        ‖z-(τ : ℂ)‖ < r → ‖w-(τ : ℂ)‖ < r →
        ‖m z-m w‖ ≤ C * ‖z-w‖ ^ ((1 : ℝ)/3) := by
  obtain ⟨L, U, hU, hLip⟩ := P.analytic.hasStrictFDerivAt.exists_lipschitzOnWith
  have hsmall : ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (τ : ℂ),
      P.parameter z ∈ U ∧ m z = P.curve (P.parameter z) ∧
        z-(τ : ℂ) = (P.coefficient : ℂ)*(P.parameter z)^P.degree ∧ 0 < (P.parameter z).im := by
    filter_upwards [P.parameter_limit.eventually hU, P.physical] with z hz hp
    exact ⟨hz, hp⟩
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  let D : ℝ := 4 / |P.coefficient|
  have hD : 0 < D := div_pos (by norm_num) (abs_pos.mpr P.coefficient_ne_zero)
  let H : ℝ := max (D ^ ((2 : ℝ)⁻¹)) (D ^ ((3 : ℝ)⁻¹))
  have hH : 0 < H := lt_max_of_lt_left (Real.rpow_pos_of_pos hD _)
  refine ⟨((L : ℝ)+1)*H, min r (1/2), mul_pos (by positivity) hH, lt_min hr (by norm_num), ?_⟩
  intro z hz w hw hzr hwr
  have hzp := hlocal ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hzr.trans_le (min_le_left _ _), hz⟩
  have hwp := hlocal ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hwr.trans_le (min_le_left _ _), hw⟩
  have hδ : ‖z-w‖ ≤ 1 := by
    have ht : ‖z-w‖ ≤ ‖z-(τ : ℂ)‖+‖w-(τ : ℂ)‖ := by
      simpa only [dist_eq_norm] using dist_triangle_right z w (τ : ℂ)
    linarith [hzr.trans_le (min_le_right _ _), hwr.trans_le (min_le_right _ _)]
  have henergy : z-w = (P.coefficient : ℂ)*((P.parameter z)^P.degree-(P.parameter w)^P.degree) := by
    linear_combination hzp.2.2.1 - hwp.2.2.1
  have hnorm : ‖(P.parameter z)^P.degree-(P.parameter w)^P.degree‖ = ‖z-w‖ / |P.coefficient| := by
    rw [henergy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    field_simp [abs_ne_zero.mpr P.coefficient_ne_zero]
  have hroot : ‖P.parameter z-P.parameter w‖ ≤ H * ‖z-w‖ ^ ((1 : ℝ)/3) := by
    rcases P.degree_cases with hk | hk
    · have hquad (v : ℂ) (hv : v ∈ ExternalAlgebraic.upper)
          (hvroot : v-(τ : ℂ)=(P.coefficient : ℂ)*(P.parameter v)^P.degree)
          (hvi : 0 < (P.parameter v).im) : 0 ≤ P.coefficient*(P.parameter v).re := by
        have hi := congrArg Complex.im hvroot
        simp only [hk, pow_two, Complex.sub_im, Complex.ofReal_im, sub_zero,
          Complex.mul_im, Complex.mul_re, Complex.ofReal_re, zero_mul, add_zero] at hi
        nlinarith [show 0 < v.im from hv]
      have hb := quadrant_square_difference P.coefficient P.coefficient_ne_zero
        (P.parameter z) (P.parameter w) hzp.2.2.2.le hwp.2.2.2.le
        (hquad z hz hzp.2.2.1 hzp.2.2.2) (hquad w hw hwp.2.2.1 hwp.2.2.2)
      have hpow : ‖P.parameter z-P.parameter w‖ ^ 2 ≤ D * ‖z-w‖ := by
        rw [hk] at hnorm
        rw [hnorm] at hb
        calc
          _ ≤ ‖z-w‖ / |P.coefficient| := hb
          _ ≤ 4 * (‖z-w‖ / |P.coefficient|) := by
            nlinarith [div_nonneg (norm_nonneg (z-w)) (abs_pos.mpr P.coefficient_ne_zero).le]
          _ = D * ‖z-w‖ := by dsimp [D]; ring
      have hh := root_bound_of_power_bound _ _ D 2 (norm_nonneg _) (norm_nonneg _) hD.le (by norm_num) hpow
      have hexp : ‖z-w‖ ^ ((2 : ℝ)⁻¹) ≤ ‖z-w‖ ^ ((1 : ℝ)/3) := by
        by_cases hzero : ‖z-w‖ = 0
        · simp [hzero]
        · exact Real.rpow_le_rpow_of_exponent_ge
            (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hδ (by norm_num)
      exact hh.trans (mul_le_mul (le_max_left _ _) hexp (by positivity) hH.le)
    · have hcone (v : ℂ) (hv : v ∈ ExternalAlgebraic.upper)
          (hvroot : v-(τ : ℂ)=(P.coefficient : ℂ)*(P.parameter v)^P.degree)
          (hvi : 0 < (P.parameter v).im) : 3*(P.parameter v).re^2 ≤ (P.parameter v).im^2 := by
        apply (cubic_upper_central_cone _ hvi ?_).le
        have hc := P.cubic_negative hk
        have hi := congrArg Complex.im hvroot
        rw [hk] at hi
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im,
          Complex.ofReal_re, zero_mul, add_zero] at hi
        nlinarith [show 0 < v.im from hv]
      have hb := central_cube_difference (P.parameter z) (P.parameter w) hzp.2.2.2.le hwp.2.2.2.le
        (hcone z hz hzp.2.2.1 hzp.2.2.2) (hcone w hw hwp.2.2.1 hwp.2.2.2)
      have hpow : ‖P.parameter z-P.parameter w‖ ^ 3 ≤ D * ‖z-w‖ := by
        rw [hk] at hnorm
        rw [hnorm] at hb
        simpa [D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
      have hh := root_bound_of_power_bound _ _ D 3 (norm_nonneg _) (norm_nonneg _) hD.le (by norm_num) hpow
      exact hh.trans (by
        simpa [one_div] using mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg (z-w)) ((3 : ℝ)⁻¹)))
  rw [hzp.2.1, hwp.2.1]
  have hlip := hLip.dist_le_mul (P.parameter z) hzp.1 (P.parameter w) hwp.1
  simp only [dist_eq_norm] at hlip
  calc
    _ ≤ (L : ℝ)*‖P.parameter z-P.parameter w‖ := hlip
    _ ≤ (L : ℝ)*(H*‖z-w‖^((1:ℝ)/3)) := mul_le_mul_of_nonneg_left hroot L.coe_nonneg
    _ ≤ _ := by nlinarith [mul_nonneg hH.le (Real.rpow_nonneg (norm_nonneg (z-w)) ((1:ℝ)/3))]

/-- Full two-point 1/3-Hölder regularity on a closed upper half-neighborhood
of the actual regular edge or cusp, including its real boundary. -/
theorem regular_frontier_one_third_holder
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
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
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ z ∈ ExternalAlgebraic.closedUpper, ∀ w ∈ ExternalAlgebraic.closedUpper,
        ‖z-(τ : ℂ)‖ < ε → ‖w-(τ : ℂ)‖ < ε →
        ‖Boundary.boundaryVector m z-Boundary.boundaryVector m w‖ ≤ C * ‖z-w‖ ^ ((1 : ℝ)/3) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨P⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  obtain ⟨C, r, hC, hr, hholder⟩ := P.upper_one_third_holder
  obtain ⟨_, hregular⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨r₀, hr₀, hreal⟩ := Metric.mem_nhds_iff.mp hregular
  let ε : ℝ := min r r₀
  have hε : 0 < ε := lt_min hr hr₀
  have hdomain (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) (hzε : ‖z-(τ : ℂ)‖<ε) :
      z ∈ Boundary.commonRegularDomain m := by
    by_cases hzi : 0 < z.im
    · exact Or.inl hzi
    · have hzero : z.im = 0 := le_antisymm (le_of_not_gt hzi) hz
      have hzreal : (z.re : ℂ)=z := Complex.ext rfl (by simpa using hzero.symm)
      have hdist : dist z.re τ < r₀ := by
        have hh := Complex.abs_re_le_norm (z-(τ : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at hh
        simpa only [Real.dist_eq] using hh.trans_lt (hzε.trans_le (min_le_right _ _))
      exact Or.inr ⟨z.re, (hreal hdist).1, hzreal⟩
  let lift : ℂ → ℝ → ℂ := fun z η => z+(η : ℂ)*Complex.I
  have hliftlim (z : ℂ) : Tendsto (lift z) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous (lift z) := by dsimp [lift]; fun_prop
    simpa [lift] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hliftup (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) {η : ℝ} (hη : 0<η) :
      lift z η ∈ ExternalAlgebraic.upper := by
    change 0 < (lift z η).im
    simpa [lift] using add_pos_of_nonneg_of_pos hz hη
  have hlim (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) (hzε : ‖z-(τ : ℂ)‖<ε) :
      Tendsto (fun η => Boundary.boundaryVector m (lift z η)) (𝓝[>] (0 : ℝ))
        (𝓝 (Boundary.boundaryVector m z)) := by
    have hb := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      z (hdomain z hz hzε)
    apply hb.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hliftlim z, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact Or.inl (hliftup z hz hη)
  refine ⟨C, ε, hC, hε, ?_⟩
  intro z hz w hw hzε hwε
  apply le_of_tendsto ((hlim z hz hzε).sub (hlim w hw hwε)).norm
  have hznear : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖lift z η-(τ : ℂ)‖<r := by
    exact ((hliftlim z).sub_const (τ : ℂ)).norm.eventually_lt_const
      (hzε.trans_le (min_le_left _ _))
  have hwnear : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖lift w η-(τ : ℂ)‖<r := by
    exact ((hliftlim w).sub_const (τ : ℂ)).norm.eventually_lt_const
      (hwε.trans_le (min_le_left _ _))
  filter_upwards [self_mem_nhdsWithin, hznear, hwnear] with η hη hzη hwη
  have hzu := hliftup z hz hη
  have hwu := hliftup w hw hη
  rw [Boundary.family_extension_agrees S a hS m hupper heq (lift z η) hzu,
    Boundary.family_extension_agrees S a hS m hupper heq (lift w η) hwu]
  have hh := hholder (lift z η) hzu (lift w η) hwu hzη hwη
  have he : lift z η-lift w η=z-w := by dsimp [lift]; ring
  simpa only [he] using hh

end NonSymmetricDyson.Full.Singularities
