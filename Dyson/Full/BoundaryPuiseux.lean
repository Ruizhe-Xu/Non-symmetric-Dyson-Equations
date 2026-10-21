import Dyson.Full.Boundary
import Dyson.Full.ExternalAlgebraic

/-!
# Boundary limits from the convergent Puiseux input

The external parameter supplies algebraic root expansions, never the
Dyson-specific boundary conclusions. The angular sign restriction and the
finite/singular alternative are deduced here.
-/

noncomputable section
open scoped Topology BigOperators
open Filter Set

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

def vertical (τ η : ℝ) : ℂ := (τ : ℂ) + (η : ℂ) * Complex.I

@[simp] theorem vertical_im (τ η : ℝ) : (vertical τ η).im = η := by
  simp [vertical]

theorem vertical_tendsto (τ : ℝ) :
    Tendsto (vertical τ) (𝓝[>] (0 : ℝ)) (𝓝 (τ : ℂ)) := by
  have hc : Continuous (vertical τ) := by unfold vertical; fun_prop
  simpa [vertical] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))

theorem vertical_eventually_upper (τ : ℝ) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), vertical τ η ∈ upper := by
  filter_upwards [self_mem_nhdsWithin] with η hη
  simpa using hη

theorem PuiseuxChart.root_vertical_tendsto {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) :
    Tendsto (fun η => p.root (vertical τ η)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hτ : (τ : ℂ) ∈ closedUpper := by simp
  have hv : Tendsto (vertical τ) (𝓝[>] (0 : ℝ)) (𝓝[closedUpper] (τ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨vertical_tendsto τ, ?_⟩
    filter_upwards [vertical_eventually_upper τ] with η hη
    exact hη.le
  simpa only [p.root_center] using (p.root_continuous _ hτ).tendsto.comp hv

/-- Nonnegative leading exponent gives a finite vertical limit by an actual
product-of-limits proof in the convergent root chart. -/
theorem PuiseuxChart.finite_limit {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (hk : 0 ≤ p.exponent) :
    ∃ b : ℂ, Tendsto (fun η => f (vertical τ η)) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  have hr := PuiseuxChart.root_vertical_tendsto p
  have hfactor := p.factor_analytic.continuousAt.tendsto.comp hr
  have hprod := (hr.pow p.exponent.toNat).mul hfactor
  refine ⟨0 ^ p.exponent.toNat * p.factor 0, hprod.congr' ?_⟩
  have hdist : Tendsto (fun η => ‖vertical τ η - (τ : ℂ)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((vertical_tendsto τ).sub (tendsto_const_nhds (x := (τ : ℂ)))).norm
  have hnear := hdist.eventually (gt_mem_nhds p.radius_pos)
  filter_upwards [vertical_eventually_upper τ, hnear] with η hη hnearη
  rw [p.expansion _ hη hnearη]
  rw [show p.root (vertical τ η) ^ p.exponent = p.root (vertical τ η) ^ p.exponent.toNat by
    simpa only [Int.toNat_of_nonneg hk] using zpow_natCast (p.root (vertical τ η)) p.exponent.toNat]
  rfl

theorem angularImag_eq (c : ℂ) (γ θ : ℝ) :
    (c * Complex.exp (((γ * θ : ℝ) : ℂ) * Complex.I)).im = angularImag c γ θ := by
  simp [angularImag, Complex.mul_im, Complex.exp_re, Complex.exp_im]

theorem ray_im (τ r θ : ℝ) : (ray τ r θ).im = r * Real.sin θ := by
  simp [ray, Complex.exp_re, Complex.exp_im]

theorem ray_half_pi (τ r : ℝ) : ray τ r (Real.pi / 2) = vertical τ r := by
  simp [ray, vertical, Complex.ofReal_div, Complex.exp_pi_div_two_mul_I]

/-- Positivity of the Pick function is passed to the normalized leading
term along every interior ray; the sign is not an external assumption. -/
theorem PuiseuxChart.leading_angular_nonnegative {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (hPick : ∀ z ∈ upper, 0 ≤ (f z).im) :
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi,
      0 ≤ angularImag (p.factor 0) ((p.exponent : ℝ) / p.denominator) θ := by
  intro θ hθ
  have hlim := Complex.continuous_im.continuousAt.tendsto.comp (p.leading_ray θ hθ)
  rw [angularImag_eq] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hz : ray τ r θ ∈ upper := by
    change 0 < (ray τ r θ).im
    rw [ray_im]
    exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  simpa only [Function.comp_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    using mul_nonneg (Real.rpow_nonneg hr.le _) (hPick _ hz)

/-- The lower exponent bound follows from the internal angular argument. -/
theorem PuiseuxChart.exponent_bound {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (hPick : ∀ z ∈ upper, 0 ≤ (f z).im)
    (hk : p.exponent < 0) : -1 ≤ (p.exponent : ℝ) / p.denominator := by
  apply negative_exponent_ge_neg_one (p.factor 0) p.factor_ne_zero
    ((p.exponent : ℝ) / p.denominator)
  · exact div_neg_of_neg_of_pos (by exact_mod_cast hk) (by exact_mod_cast p.denominator_pos)
  · exact PuiseuxChart.leading_angular_nonnegative p hPick

theorem tendsto_rpow_negative_zero {γ : ℝ} (hγ : γ < 0) :
    Tendsto (fun r : ℝ => r ^ γ) (𝓝[>] (0 : ℝ)) atTop := by
  convert (tendsto_rpow_atTop (neg_pos.mpr hγ)).comp tendsto_inv_nhdsGT_zero using 1
  funext r
  change r ^ γ = r⁻¹ ^ (-γ)
  rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]

/-- A negative leading exponent forces the *real imaginary part* to tend
to positive infinity. This is not a statement that a complex number tends
to infinity in its ordinary topology. -/
theorem PuiseuxChart.imaginary_diverges {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (hPick : ∀ z ∈ upper, 0 ≤ (f z).im)
    (hk : p.exponent < 0) :
    Tendsto (fun η => (f (vertical τ η)).im) (𝓝[>] (0 : ℝ)) atTop := by
  let γ : ℝ := (p.exponent : ℝ) / p.denominator
  have hγ : γ < 0 :=
    div_neg_of_neg_of_pos (by exact_mod_cast hk) (by exact_mod_cast p.denominator_pos)
  have hangle : Real.pi / 2 ∈ Ioo (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hcpos := angularImag_strict (p.factor 0) p.factor_ne_zero γ
    (ne_of_lt hγ) (PuiseuxChart.leading_angular_nonnegative p hPick) (Real.pi / 2) hangle
  have hlim := Complex.continuous_im.continuousAt.tendsto.comp
    (p.leading_ray (Real.pi / 2) hangle)
  have hnormal : Tendsto (fun η : ℝ => η ^ (-γ) * (f (vertical τ η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (angularImag (p.factor 0) γ (Real.pi / 2))) := by
    rw [angularImag_eq] at hlim
    simpa only [Function.comp_def, ray_half_pi, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, neg_div, γ] using hlim
  have hdiv := hnormal.pos_mul_atTop hcpos (tendsto_rpow_negative_zero hγ)
  apply hdiv.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hcancel : η ^ (-γ) * η ^ γ = 1 := by
    rw [← Real.rpow_add hη, neg_add_cancel, Real.rpow_zero]
  calc
    η ^ (-γ) * (f (vertical τ η)).im * η ^ γ =
        (η ^ (-γ) * η ^ γ) * (f (vertical τ η)).im := by ring
    _ = (f (vertical τ η)).im := by rw [hcancel, one_mul]

def singularSet (f : ℂ → ℂ) : Set ℝ :=
  {τ | Tendsto (fun η => ‖f (vertical τ η)‖) (𝓝[>] (0 : ℝ)) atTop}

theorem norm_diverges_of_imaginary {f : ℂ → ℂ} {τ : ℝ}
    (h : Tendsto (fun η => (f (vertical τ η)).im) (𝓝[>] (0 : ℝ)) atTop) :
    τ ∈ singularSet f := by
  apply tendsto_atTop_mono (fun η => ?_) h
  exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

theorem holomorphicAcross_finite_limit {f : ℂ → ℂ} {τ : ℝ}
    (h : HolomorphicAcross f τ) :
    ∃ b : ℂ, Tendsto (fun η => f (vertical τ η)) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  obtain ⟨g, hg, heq⟩ := h
  refine ⟨g τ, (hg.continuousAt.tendsto.comp (vertical_tendsto τ)).congr' ?_⟩
  filter_upwards [(vertical_tendsto τ).eventually heq, vertical_eventually_upper τ] with η he hη
  exact (he hη).symm

/-- The singular set is finite, the two definitions of singularity agree,
and every remaining point has a finite vertical boundary value. All three
claims are deduced from the actual convergent algebraic chart. -/
theorem algebraic_boundary_alternative (external : ConvergentPuiseuxTheory)
    (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f upper) (halg : AlgebraicOnUpper f)
    (hPick : ∀ z ∈ upper, 0 < (f z).im) :
    (singularSet f).Finite ∧
    (∀ τ, τ ∈ singularSet f ↔
      Tendsto (fun η => (f (vertical τ η)).im) (𝓝[>] (0 : ℝ)) atTop) ∧
    (∀ τ ∉ singularSet f, ∃ b : ℂ,
      Tendsto (fun η => f (vertical τ η)) (𝓝[>] (0 : ℝ)) (𝓝 b)) := by
  have hI : Complex.I ∈ upper := by simp
  have hnonzero : f Complex.I ≠ 0 := by
    intro hz
    have hp := hPick _ hI
    simpa [hz] using hp
  obtain ⟨⟨E, hE, hext⟩, hcharts⟩ := external f ha halg ⟨Complex.I, hI, hnonzero⟩
  have hsubset : singularSet f ⊆ E := by
    intro τ hτ
    by_contra hnot
    obtain ⟨b, hb⟩ := holomorphicAcross_finite_limit (hext τ hnot)
    exact not_tendsto_atTop_of_tendsto_nhds hb.norm hτ
  refine ⟨hE.subset hsubset, ?_, ?_⟩
  · intro τ
    constructor
    · intro hs
      obtain ⟨p⟩ := hcharts τ
      by_cases hk : 0 ≤ p.exponent
      · obtain ⟨b, hb⟩ := PuiseuxChart.finite_limit p hk
        exact False.elim (not_tendsto_atTop_of_tendsto_nhds hb.norm hs)
      · exact PuiseuxChart.imaginary_diverges p (fun z hz => (hPick z hz).le) (lt_of_not_ge hk)
    · exact norm_diverges_of_imaginary
  · intro τ hτ
    obtain ⟨p⟩ := hcharts τ
    by_cases hk : 0 ≤ p.exponent
    · exact PuiseuxChart.finite_limit p hk
    · exact False.elim (hτ (norm_diverges_of_imaginary
        (PuiseuxChart.imaginary_diverges p (fun z hz => (hPick z hz).le) (lt_of_not_ge hk))))

end NonSymmetricDyson.Full.Boundary

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

/-- The same chart gives a full upper-half-plane limit, not only a vertical
one. This is the ingredient needed to glue a continuous extension. -/
theorem PuiseuxChart.full_finite_limit {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (hk : 0 ≤ p.exponent) :
    ∃ b : ℂ, Tendsto f (𝓝[upper] (τ : ℂ)) (𝓝 b) := by
  have hτ : (τ : ℂ) ∈ closedUpper := by simp
  have hr : Tendsto p.root (𝓝[upper] (τ : ℂ)) (𝓝 0) := by
    simpa only [p.root_center] using
      ((p.root_continuous _ hτ).mono (show upper ⊆ closedUpper from fun z hz => (show 0 < z.im from hz).le)).tendsto
  have hprod := (hr.pow p.exponent.toNat).mul
    (p.factor_analytic.continuousAt.tendsto.comp hr)
  refine ⟨0 ^ p.exponent.toNat * p.factor 0, hprod.congr' ?_⟩
  have hnear : ∀ᶠ z in 𝓝[upper] (τ : ℂ), ‖z - (τ : ℂ)‖ < p.radius := by
    have hmem := Metric.ball_mem_nhds (τ : ℂ) p.radius_pos
    filter_upwards [nhdsWithin_le_nhds hmem] with z hz
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  filter_upwards [self_mem_nhdsWithin, hnear] with z hz hnearz
  rw [p.expansion z hz hnearz]
  rw [show p.root z ^ p.exponent = p.root z ^ p.exponent.toNat by
    simpa only [Int.toNat_of_nonneg hk] using zpow_natCast (p.root z) p.exponent.toNat]
  rfl

def regularDomain (f : ℂ → ℂ) : Set ℂ :=
  upper ∪ Complex.ofReal '' (singularSet f)ᶜ

def boundaryExtension (f : ℂ → ℂ) : ℂ → ℂ := extendFrom upper f

theorem real_mem_closure_upper (τ : ℝ) : (τ : ℂ) ∈ closure upper :=
  mem_closure_of_tendsto (vertical_tendsto τ) (vertical_eventually_upper τ)

theorem regularDomain_subset_closure (f : ℂ → ℂ) :
    regularDomain f ⊆ closure upper := by
  rintro z (hz | ⟨τ, _, rfl⟩)
  · exact subset_closure hz
  · exact real_mem_closure_upper τ

/-- The genuine upper-half-plane function extends continuously precisely
on the asserted regular domain. `extendFrom` is used only after existence
of all its relevant limits has been proved. -/
theorem algebraic_continuous_extension (external : ConvergentPuiseuxTheory)
    (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f upper) (halg : AlgebraicOnUpper f)
    (hPick : ∀ z ∈ upper, 0 < (f z).im) :
    ContinuousOn (boundaryExtension f) (regularDomain f) ∧
    (∀ z ∈ upper, boundaryExtension f z = f z) ∧
    (∀ τ ∉ singularSet f,
      Tendsto (fun η => f (vertical τ η)) (𝓝[>] (0 : ℝ))
        (𝓝 (boundaryExtension f (τ : ℂ)))) := by
  have hI : Complex.I ∈ upper := by simp
  have hnonzero : f Complex.I ≠ 0 := by
    intro hz
    have hp := hPick _ hI
    simpa [hz] using hp
  obtain ⟨_, hcharts⟩ := external f ha halg ⟨Complex.I, hI, hnonzero⟩
  have hlimits : ∀ z ∈ regularDomain f, ∃ b : ℂ, Tendsto f (𝓝[upper] z) (𝓝 b) := by
    rintro z (hz | ⟨τ, hτ, rfl⟩)
    · exact ⟨f z, (ha z hz).continuousAt.continuousWithinAt⟩
    · obtain ⟨p⟩ := hcharts τ
      have hk : 0 ≤ p.exponent := by
        by_contra hk
        exact hτ (norm_diverges_of_imaginary
          (PuiseuxChart.imaginary_diverges p (fun z hz => (hPick z hz).le) (lt_of_not_ge hk)))
      exact PuiseuxChart.full_finite_limit p hk
  refine ⟨continuousOn_extendFrom (regularDomain_subset_closure f) hlimits,
    extendFrom_extends ha.continuousOn, ?_⟩
  intro τ hτ
  have hτdom : (τ : ℂ) ∈ regularDomain f := Or.inr ⟨τ, hτ, rfl⟩
  apply (tendsto_extendFrom (hlimits _ hτdom)).comp
  exact tendsto_nhdsWithin_iff.mpr ⟨vertical_tendsto τ, vertical_eventually_upper τ⟩

/-- A uniform bound along the vertical line excludes a singular point,
including an endpoint of a strip. -/
theorem not_singular_of_bounded {f : ℂ → ℂ} {τ M : ℝ}
    (hbound : ∀ η : ℝ, 0 < η → ‖f (vertical τ η)‖ ≤ M) :
    τ ∉ singularSet f := by
  intro hs
  have hlarge := hs.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖f (vertical τ η)‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hbound η hη
  obtain ⟨η, hηlarge, hηsmall⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hηsmall) hηlarge

end NonSymmetricDyson.Full.Boundary
