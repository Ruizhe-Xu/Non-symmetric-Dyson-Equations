import Mathlib

/-! Quantitative extraction of the density from an exact monomial
parametrization. The hypotheses are numerical identities and a Taylor error
bound for the actual complex value; no density asymptotic is assumed. -/

noncomputable section

namespace NonSymmetricDyson.Full.Singularities

theorem imaginary_taylor_remainder_bound (M s : ℂ) (m₀ d C : ℝ)
    (herror : ‖M - (m₀ : ℂ) - (d : ℂ) * s‖ ≤ C * ‖s‖ ^ 2) :
    |M.im - d * s.im| ≤ C * ‖s‖ ^ 2 := by
  have hh := (Complex.abs_im_le_norm (M - (m₀ : ℂ) - (d : ℂ) * s)).trans herror
  simpa only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, sub_zero] using hh

/-- The density coefficient and exponent follow from the monomial parameter
without using a prior Hölder estimate. Degrees two and three are both covered. -/
theorem density_from_monomial_parametrization
    (M w ζ : ℂ) (m₀ d C c a : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hc : c ≠ 0) (hk : k ≠ 0) (hζ : ‖ζ‖ = 1)
    (hw : w = (c : ℂ) * (ζ * (a : ℂ)) ^ k)
    (herror : ‖M - (m₀ : ℂ) - (d : ℂ) * (ζ * (a : ℂ))‖ ≤
      C * ‖ζ * (a : ℂ)‖ ^ 2) :
    |M.im - d * ζ.im * (‖w‖ / |c|) ^ ((k : ℝ)⁻¹)| ≤
      C * ((‖w‖ / |c|) ^ ((k : ℝ)⁻¹)) ^ 2 := by
  have hsnorm : ‖ζ * (a : ℂ)‖ = a := by
    rw [norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hwnorm : ‖w‖ = |c| * a ^ k := by
    rw [hw, norm_mul, norm_pow, hsnorm, Complex.norm_real, Real.norm_eq_abs]
  have hroot : (‖w‖ / |c|) ^ ((k : ℝ)⁻¹) = a := by
    rw [hwnorm, mul_div_cancel_left₀ (a ^ k) (abs_ne_zero.mpr hc)]
    exact Real.pow_rpow_inv_natCast ha hk
  rw [hroot]
  have hh := imaginary_taylor_remainder_bound M (ζ * (a : ℂ)) m₀ d C herror
  simpa only [hsnorm, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    mul_zero, zero_add, mul_assoc] using hh

/-- A leading positive imaginary coefficient gives an explicit two-sided
density scale on a sufficiently short punctured interval. -/
theorem positive_density_scale (v D C a : ℝ) (ha : 0 ≤ a) (hD : 0 < D)
    (herror : |v - D * a| ≤ C * a ^ 2) (hsmall : C * a ≤ D / 2) :
    D / 2 * a ≤ v ∧ v ≤ (3 * D / 2) * a := by
  have hlo := (abs_le.mp herror).1
  have hhi := (abs_le.mp herror).2
  have he := mul_le_mul_of_nonneg_right hsmall ha
  constructor <;> nlinarith

def cuspPositiveRootUnit : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩
def cuspNegativeRootUnit : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

@[simp] theorem cuspPositiveRootUnit_im : cuspPositiveRootUnit.im = Real.sqrt 3 / 2 := rfl
@[simp] theorem cuspNegativeRootUnit_im : cuspNegativeRootUnit.im = Real.sqrt 3 / 2 := rfl

theorem cuspPositiveRootUnit_norm : ‖cuspPositiveRootUnit‖ = 1 := by
  have hn : ‖cuspPositiveRootUnit‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [cuspPositiveRootUnit]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [norm_nonneg cuspPositiveRootUnit]

theorem cuspNegativeRootUnit_norm : ‖cuspNegativeRootUnit‖ = 1 := by
  have hn : ‖cuspNegativeRootUnit‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [cuspNegativeRootUnit]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [norm_nonneg cuspNegativeRootUnit]

theorem cuspPositiveRootUnit_cube : cuspPositiveRootUnit ^ 3 = -1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp only [pow_succ, pow_zero, mul_one, Complex.mul_re,
    Complex.mul_im, cuspPositiveRootUnit,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
  · nlinarith
  · linear_combination -(Real.sqrt 3 / 8) * hs

theorem cuspNegativeRootUnit_cube : cuspNegativeRootUnit ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp only [pow_succ, pow_zero, mul_one, Complex.mul_re,
    Complex.mul_im, cuspNegativeRootUnit,
    Complex.one_re, Complex.one_im]
  · nlinarith
  · linear_combination -(Real.sqrt 3 / 8) * hs

end NonSymmetricDyson.Full.Singularities
