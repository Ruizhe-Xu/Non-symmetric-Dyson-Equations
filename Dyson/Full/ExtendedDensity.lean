import Dyson.Full.MainDecomposition
import Dyson.Full.RationalAlgebraicity

/-! Pointwise extended-valued imaginary boundary limits. In contrast to a
Radon--Nikodym representative defined only almost everywhere, these limits
also specify a value at each singular point. -/

noncomputable section
open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

/-- The canonical extended nonnegative imaginary boundary representative.
Its existence is proved below for the atom-removed algebraic transform. -/
def extendedDensity (h : ℂ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun η => ENNReal.ofReal ((h (vertical x η)).im / Real.pi))

theorem extendedDensity_eq_of_finite_limit (h : ℂ → ℂ) (x : ℝ) (L : ℝ)
    (hlim : Tendsto (fun η => (h (vertical x η)).im) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    extendedDensity h x = ENNReal.ofReal (L / Real.pi) :=
  (ENNReal.tendsto_ofReal (hlim.div_const Real.pi)).limUnder_eq

theorem extendedDensity_eq_top_of_diverges (h : ℂ → ℂ) (x : ℝ)
    (hlim : Tendsto (fun η => (h (vertical x η)).im) (𝓝[>] (0 : ℝ)) atTop) :
    extendedDensity h x = ∞ := by
  apply Filter.Tendsto.limUnder_eq
  apply ENNReal.tendsto_ofReal_atTop.comp
  exact hlim.atTop_div_const Real.pi_pos

/-- The finite or infinite alternative follows from the convergent series
and the internally proved Pick-sector sign restriction. -/
theorem algebraic_extended_density_limit (puiseux : ConvergentPuiseuxTheory)
    (h : ℂ → ℂ) (ha : AnalyticOnNhd ℂ h upper) (halg : AlgebraicOnUpper h)
    (hPick : (∀ z ∈ upper, h z = 0) ∨ (∀ z ∈ upper, 0 < (h z).im))
    (x : ℝ) :
    Tendsto (fun η => ENNReal.ofReal ((h (vertical x η)).im / Real.pi))
      (𝓝[>] (0 : ℝ)) (𝓝 (extendedDensity h x)) := by
  apply tendsto_nhds_limUnder
  rcases hPick with hz | hp
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [vertical_eventually_upper x] with η hη
    simp [hz _ hη]
  · have hI : Complex.I ∈ upper := by simp
    have hne : h Complex.I ≠ 0 := by
      intro he
      have := hp Complex.I hI
      simp [he] at this
    obtain ⟨p⟩ := (puiseux h ha halg ⟨Complex.I, hI, hne⟩).2 x
    by_cases hk : 0 ≤ p.exponent
    · obtain ⟨b, hb⟩ := PuiseuxChart.finite_limit p hk
      refine ⟨ENNReal.ofReal (b.im / Real.pi), ?_⟩
      exact ENNReal.tendsto_ofReal
        ((Complex.continuous_im.continuousAt.tendsto.comp hb).div_const Real.pi)
    · refine ⟨∞, ?_⟩
      apply ENNReal.tendsto_ofReal_atTop.comp
      exact (PuiseuxChart.imaginary_diverges p (fun z hz => (hp z hz).le)
        (lt_of_not_ge hk)).atTop_div_const Real.pi_pos

/-- Real atomic rational terms have a real finite boundary value away
from their poles, hence contribute zero to the boundary imaginary part. -/
theorem finite_pole_imaginary_limit_zero (A : Finset ℝ) (c : ℝ → ℝ)
    (x : ℝ) (hx : x ∉ A) :
    Tendsto (fun η => (∑ τ ∈ A, (c τ : ℂ) / ((τ : ℂ) - vertical x η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsum : Tendsto
      (fun η => ∑ τ ∈ A, (c τ : ℂ) / ((τ : ℂ) - vertical x η))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ τ ∈ A, (c τ : ℂ) / ((τ : ℂ) - (x : ℂ)))) := by
    apply tendsto_finset_sum
    intro τ hτ
    apply tendsto_const_nhds.div (tendsto_const_nhds.sub (vertical_tendsto x))
    intro he
    have hτx : τ = x := by exact_mod_cast sub_eq_zero.mp he
    exact hx (hτx ▸ hτ)
  have hreal : (∑ τ ∈ A, (c τ : ℂ) / ((τ : ℂ) - (x : ℂ))).im = 0 := by
    simp [Complex.div_im]
  simpa only [Function.comp_def, hreal] using
    Complex.continuous_im.continuousAt.tendsto.comp hsum

/-- Subtraction of atomic poles does not change the regular imaginary
boundary density. No informal cancellation at a singular point is used. -/
theorem extendedDensity_sub_poles_regular (f : ℂ → ℂ)
    (A : Finset ℝ) (c : ℝ → ℝ) (x : ℝ) (hx : x ∉ A) (b : ℂ)
    (hb : Tendsto (fun η => f (vertical x η)) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    extendedDensity (fun z => f z - ∑ τ ∈ A, (c τ : ℂ) / ((τ : ℂ)-z)) x =
      ENNReal.ofReal (b.im / Real.pi) := by
  apply extendedDensity_eq_of_finite_limit
  have hf := Complex.continuous_im.continuousAt.tendsto.comp hb
  have hp := finite_pole_imaginary_limit_zero A c x hx
  simpa only [Complex.sub_im, Function.comp_def, sub_zero] using hf.sub hp

/-- Atomlessness excludes a residual simple pole. Combined with the
Pick-sector bound, every negative leading exponent is strictly above -1. -/
theorem PuiseuxChart.exponent_gt_neg_one_of_zero_atom_limit
    {h : ℂ → ℂ} {x : ℝ} (p : PuiseuxChart h x)
    (hPick : ∀ z ∈ upper, 0 ≤ (h z).im)
    (hzero : Tendsto (fun η => η * (h (vertical x η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    -1 < (p.exponent : ℝ) / p.denominator := by
  by_cases hk : 0 ≤ p.exponent
  · have hnonneg : 0 ≤ (p.exponent : ℝ) / p.denominator :=
      div_nonneg (by exact_mod_cast hk) (by positivity)
    linarith
  · have hkn : p.exponent < 0 := lt_of_not_ge hk
    have hge := PuiseuxChart.exponent_bound p hPick hkn
    apply lt_of_le_of_ne hge
    intro heq
    have hγ : (p.exponent : ℝ) / p.denominator = -1 := heq.symm
    have hangle : Real.pi / 2 ∈ Ioo (0 : ℝ) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have hpos := angularImag_strict (p.factor 0) p.factor_ne_zero
      ((p.exponent : ℝ) / p.denominator) (by rw [hγ]; norm_num)
      (PuiseuxChart.leading_angular_nonnegative p hPick) (Real.pi / 2) hangle
    have hl := Complex.continuous_im.continuousAt.tendsto.comp
      (p.leading_ray (Real.pi / 2) hangle)
    rw [angularImag_eq] at hl
    have hn : -(p.exponent : ℝ) / p.denominator = 1 := by rw [neg_div, hγ]; norm_num
    have hlead : Tendsto (fun η => η * (h (vertical x η)).im)
        (𝓝[>] (0 : ℝ))
        (𝓝 (angularImag (p.factor 0) ((p.exponent : ℝ) / p.denominator) (Real.pi / 2))) := by
      simpa only [Function.comp_def, ray_half_pi, hn, Real.rpow_one,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hl
    have he := tendsto_nhds_unique hlead hzero
    linarith

end NonSymmetricDyson.Full.Boundary
