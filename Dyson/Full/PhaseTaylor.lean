import Mathlib

/-! Exact scalar phase expansion for the actual conjugate ratio. The cubic
remainder follows from the normalized real/imaginary unit-circle identity and
the sign of the real part; it is not an external perturbation assumption. -/
noncomputable section
namespace NonSymmetricDyson.Full.PhaseTaylor

theorem complex_norm_two : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num

/-- Normalized real and imaginary parts satisfy the exact unit-circle law. -/
theorem normalized_circle (m : ℂ) (hm : m ≠ 0) :
    (m.re/‖m‖)^2+(m.im/‖m‖)^2 = 1 := by
  have hn : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  have hsq : ‖m‖^2 = m.re^2+m.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  field_simp
  nlinarith

/-- The conjugate ratio has no hidden analytic remainder before replacing the
normalized real part by its sign. -/
theorem phase_exact (m : ℂ) (hm : m ≠ 0) :
    star m / m = 1 - 2*((m.im/‖m‖:ℝ):ℂ)^2 -
      2*Complex.I*((m.re/‖m‖:ℝ):ℂ)*((m.im/‖m‖:ℝ):ℂ) := by
  have hn : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  have hsq : Complex.normSq m = ‖m‖^2 := Complex.normSq_eq_norm_sq m
  have hsqR : ‖m‖^2 = m.re^2+m.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  apply Complex.ext
  · simp [Complex.div_re, hsq, pow_two, Complex.mul_re, Complex.mul_im]
    field_simp [hn]
    nlinarith [hsqR]
  · simp [Complex.div_im, hsq, pow_two, Complex.mul_im, Complex.mul_re]
    field_simp [hn]
    <;> ring

/-- If p is the sign of the normalized real part, its deviation from p is
quadratic in the normalized imaginary part. -/
theorem real_part_sign_error (x v p : ℝ) (hp : p^2=1)
    (hsign : 0 ≤ p*x) (hcircle : x^2+v^2=1) : |x-p| ≤ v^2 := by
  have hpabs : |p| = 1 := by nlinarith [sq_abs p, abs_nonneg p]
  have hy2 : (p*x)^2+v^2=1 := by nlinarith [sq_nonneg v]
  have hy1 : p*x ≤ 1 := by nlinarith [sq_nonneg v]
  have habs : |x-p| = 1-p*x := by
    have hh : p*(x-p)=p*x-1 := by nlinarith
    calc
      |x-p| = |p*(x-p)| := by rw [abs_mul, hpabs, one_mul]
      _ = |p*x-1| := by rw [hh]
      _ = 1-p*x := by rw [abs_of_nonpos (by linarith)]; ring
  rw [habs]
  nlinarith [mul_nonneg hsign (sub_nonneg.mpr hy1)]

/-- The entrywise phase expansion has a genuine cubic error with constant2. -/
theorem phase_cubic_error (m : ℂ) (hm : m ≠ 0) (p : ℝ)
    (hp : p^2=1) (hsign : 0 ≤ p*m.re) :
    ‖star m/m - (1 - 2*Complex.I*(p:ℂ)*((m.im/‖m‖:ℝ):ℂ) -
      2*((m.im/‖m‖:ℝ):ℂ)^2)‖ ≤ 2*|m.im/‖m‖|^3 := by
  let v : ℝ := m.im/‖m‖
  let x : ℝ := m.re/‖m‖
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hsign' : 0 ≤ p*x := by
    dsimp [x]
    rw [← mul_div_assoc]
    exact div_nonneg hsign hn.le
  have hx := real_part_sign_error x v p hp hsign' (normalized_circle m hm)
  have he : star m/m - (1 - 2*Complex.I*(p:ℂ)*(v:ℂ) - 2*(v:ℂ)^2) =
      -2*Complex.I*((x-p:ℝ):ℂ)*(v:ℂ) := by
    rw [phase_exact m hm]
    dsimp [x,v]
    push_cast
    ring
  change ‖star m/m - (1 - 2*Complex.I*(p:ℂ)*(v:ℂ) - 2*(v:ℂ)^2)‖ ≤ _
  rw [he]
  calc
    ‖-2*Complex.I*((x-p:ℝ):ℂ)*(v:ℂ)‖ = 2*|x-p| *|v| := by
      simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, complex_norm_two, mul_one]
    _ ≤ 2*v^2*|v| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ = 2*|v|^3 := by rw [← sq_abs v]; ring

/-- The quadratic polynomial appearing in the phase expansion. -/
def phasePolynomial (p v : ℝ) : ℂ :=
  1 - 2*Complex.I*(p:ℂ)*(v:ℂ) - 2*(v:ℂ)^2

theorem phasePolynomial_difference_bound (p v a : ℝ) (hp : p^2=1) :
    ‖phasePolynomial p v - phasePolynomial p a‖ ≤
      2*|v-a| *(1+|v|+|a|) := by
  have hpabs : |p|=1 := by nlinarith [sq_abs p, abs_nonneg p]
  have he : phasePolynomial p v - phasePolynomial p a =
      -2*Complex.I*(p:ℂ)*((v-a:ℝ):ℂ) - 2*((v-a:ℝ):ℂ)*((v+a:ℝ):ℂ) := by
    unfold phasePolynomial
    push_cast
    ring
  rw [he]
  calc
    _ ≤ 2*|v-a| + 2*|v-a| * |v+a| := by
      simpa only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, complex_norm_two, hpabs, mul_one] using
        norm_sub_le (-2*Complex.I*(p:ℂ)*((v-a:ℝ):ℂ))
          (2*((v-a:ℝ):ℂ)*((v+a:ℝ):ℂ))
    _ ≤ 2*|v-a| *(1+|v|+|a|) := by
      have h := mul_le_mul_of_nonneg_left (abs_add_le v a)
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg (v-a)))
      nlinarith

/-- A cubic error after v=δr+ηt is O(δ³+η), uniformly for bounded r,t and
0≤δ,η≤1. The explicit constants do not depend on δ or η. -/
theorem phase_substitution_error (m : ℂ) (hm : m ≠ 0) (p δ η r t R T : ℝ)
    (hp : p^2=1) (hsign : 0 ≤ p*m.re)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hr : |r| ≤ R) (ht : |t| ≤ T)
    (hv : m.im/‖m‖ = δ*r+η*t) :
    ‖star m/m - phasePolynomial p (δ*r)‖ ≤
      (1+8*(R^3+T^3)+2*T*(2+R))*(δ^3+η) := by
  let v : ℝ := m.im/‖m‖
  have hn : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hv1 : |v| ≤ 1 := by
    dsimp [v]
    rw [abs_div, abs_of_pos hn]
    exact (div_le_one hn).mpr (Complex.abs_im_le_norm _)
  have ha : |δ*r| ≤ R := by
    rw [abs_mul, abs_of_nonneg hδ]
    exact (mul_le_mul_of_nonneg_left hr hδ).trans (mul_le_of_le_one_left hR hδ1)
  have hdiff : |v-δ*r| ≤ η*T := by
    have he : v-δ*r=η*t := by dsimp [v]; rw [hv]; ring
    rw [he, abs_mul, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left ht hη
  have hvs : |v| ≤ δ*R+η*T := by
    dsimp [v]
    rw [hv]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg hη]
      exact add_le_add (mul_le_mul_of_nonneg_left hr hδ) (mul_le_mul_of_nonneg_left ht hη))
  have hηcube : η^3 ≤ η := by
    have hs := pow_le_pow_left₀ hη hη1 2
    have hh := mul_le_mul_of_nonneg_left hs hη
    norm_num at hh
    nlinarith
  have hbin : (δ*R+η*T)^3 ≤ 4*((δ*R)^3+(η*T)^3) := by
    have hh := mul_nonneg (add_nonneg (mul_nonneg hδ hR) (mul_nonneg hη hT))
      (sq_nonneg (δ*R-η*T))
    nlinarith
  have hcub : |v|^3 ≤ 4*(R^3*δ^3+T^3*η) := by
    calc
      |v|^3 ≤ (δ*R+η*T)^3 := pow_le_pow_left₀ (abs_nonneg _) hvs 3
      _ ≤ 4*((δ*R)^3+(η*T)^3) := hbin
      _ = 4*(R^3*δ^3+T^3*η^3) := by ring
      _ ≤ 4*(R^3*δ^3+T^3*η) := by gcongr
  have hlip : ‖phasePolynomial p v-phasePolynomial p (δ*r)‖ ≤ 2*η*T*(2+R) := by
    apply (phasePolynomial_difference_bound p v (δ*r) hp).trans
    calc
      2*|v-δ*r| *(1+|v|+|δ*r|) ≤ 2*(η*T)*(1+1+R) := by gcongr
      _ = _ := by ring
  have hcubic : ‖star m/m-phasePolynomial p v‖ ≤ 2*|v|^3 := phase_cubic_error m hm p hp hsign
  calc
    ‖star m/m-phasePolynomial p (δ*r)‖ ≤
        ‖star m/m-phasePolynomial p v‖ + ‖phasePolynomial p v-phasePolynomial p (δ*r)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*|v|^3+2*η*T*(2+R) := add_le_add hcubic hlip
    _ ≤ 8*(R^3*δ^3+T^3*η)+2*η*T*(2+R) := by nlinarith
    _ ≤ (1+8*(R^3+T^3)+2*T*(2+R))*(δ^3+η) := by
      have h1 := mul_nonneg (pow_nonneg hR 3) hη
      have h2 := mul_nonneg (pow_nonneg hT 3) (pow_nonneg hδ 3)
      have h3 := mul_nonneg (mul_nonneg hT (show 0 ≤ 2+R by linarith)) (pow_nonneg hδ 3)
      nlinarith [pow_nonneg hδ 3]

/-- The sign condition needed above holds near any nonzero real boundary
value with the same prescribed sign. -/
theorem eventually_real_sign {X : Type*} {L : Filter X}
    (m : X → ℂ) (m₀ : ℂ) (p : ℝ)
    (hlim : Filter.Tendsto m L (nhds m₀)) (hpos : 0 < p*m₀.re) :
    ∀ᶠ x in L, 0 < p*(m x).re := by
  have ht : Filter.Tendsto (fun x => p*(m x).re) L (nhds (p*m₀.re)) :=
    tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp hlim)
  exact ht.eventually (isOpen_Ioi.mem_nhds hpos)

end NonSymmetricDyson.Full.PhaseTaylor
