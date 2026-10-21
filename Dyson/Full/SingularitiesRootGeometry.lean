import Dyson.Full.SingularitiesDensity

noncomputable section
namespace NonSymmetricDyson.Full.Singularities

/-- The boundary of the physical central cubic cone has fixed imaginary
angle. The real cubic root is excluded by the cone inequality itself. -/
theorem cubic_boundary_im_norm (s : ℂ) (hy : 0 ≤ s.im)
    (hcone : 3 * s.re ^ 2 ≤ s.im ^ 2) (hreal : (s ^ 3).im = 0) :
    s.im = Real.sqrt 3 / 2 * ‖s‖ := by
  have he : (s ^ 3).im = s.im * (3 * s.re ^ 2 - s.im ^ 2) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have hsq : s.im ^ 2 = 3 * s.re ^ 2 := by
    rw [he] at hreal
    rcases mul_eq_zero.mp hreal with h | h
    · nlinarith [sq_nonneg s.re]
    · linarith
  have hn : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hscaled : (Real.sqrt 3 / 2 * ‖s‖) ^ 2 = s.im ^ 2 := by
    calc
      _ = (Real.sqrt 3) ^ 2 / 4 * ‖s‖ ^ 2 := by ring
      _ = s.im ^ 2 := by rw [hsqrt, hn]; nlinarith
  have hnon : 0 ≤ Real.sqrt 3 / 2 * ‖s‖ := by positivity
  nlinarith

/-- The modulus of a monomial parameter is the positive real power of the
energy modulus, including the zero energy. -/
theorem monomial_parameter_norm (c w : ℝ) (s : ℂ) (k : ℕ)
    (hc : c ≠ 0) (hk : k ≠ 0) (hroot : (w : ℂ) = (c : ℂ) * s ^ k) :
    ‖s‖ = (|w| / |c|) ^ ((k : ℝ)⁻¹) := by
  have hn := congrArg norm hroot
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn, mul_div_cancel_left₀ (‖s‖ ^ k) (abs_ne_zero.mpr hc)]
  exact (Real.pow_rpow_inv_natCast (norm_nonneg s) hk).symm

/-- On the interior side of a quadratic edge the physical boundary
parameter is purely imaginary with imaginary part equal to its modulus. -/
theorem square_boundary_inside_im_norm (c w : ℝ) (s : ℂ)
    (hc : c ≠ 0) (hy : 0 ≤ s.im) (hside : c * w < 0)
    (hroot : (w : ℂ) = (c : ℂ) * s ^ 2) : s.im = ‖s‖ := by
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero] at hre him
  have hxy : s.re * s.im = 0 := by
    have hh : c * (s.re * s.im) = 0 := by nlinarith [him]
    exact (mul_eq_zero.mp hh).resolve_left hc
  have hx : s.re = 0 := by
    rcases mul_eq_zero.mp hxy with h | h
    · exact h
    · rw [h] at hre
      have hh : c * w = c ^ 2 * s.re ^ 2 := by rw [hre]; ring
      rw [hh] at hside
      exact False.elim ((not_lt_of_ge (mul_nonneg (sq_nonneg c) (sq_nonneg s.re))) hside)
  have hn : ‖s‖ ^ 2 = s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hx]
    ring
  nlinarith [norm_nonneg s]

/-- On the exterior side the quadratic parameter is real. Real reflection
of the analytic curve then gives an exactly vanishing density. -/
theorem square_boundary_outside_real (c w : ℝ) (s : ℂ)
    (hc : c ≠ 0) (hside : 0 < c * w)
    (hroot : (w : ℂ) = (c : ℂ) * s ^ 2) : s.im = 0 := by
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero] at hre him
  have hxy : s.re * s.im = 0 := by
    have hh : c * (s.re * s.im) = 0 := by nlinarith [him]
    exact (mul_eq_zero.mp hh).resolve_left hc
  rcases mul_eq_zero.mp hxy with h | h
  · rw [h] at hre
    have hh : c * w = -(c ^ 2 * s.im ^ 2) := by rw [hre]; ring
    rw [hh] at hside
    exact False.elim ((not_lt_of_ge (neg_nonpos.mpr (mul_nonneg (sq_nonneg c) (sq_nonneg s.im)))) hside)
  · exact h

end NonSymmetricDyson.Full.Singularities
