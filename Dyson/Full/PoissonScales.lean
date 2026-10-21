import Dyson.Full.Poisson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace NonSymmetricDyson.Full.Poisson

/-- The fixed finite fractional Cauchy moment; no edge or cusp conclusion is
assumed in this definition. -/
def fractionalMomentIntegrand (α x : ℝ) : ℝ := |x| ^ α / (1 + x^2)
def fractionalMoment (α : ℝ) : ℝ := ∫ x, fractionalMomentIntegrand α x

theorem fractionalMoment_integrable {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Integrable (fractionalMomentIntegrand α) := by
  have hc : Continuous (fractionalMomentIntegrand α) := by
    unfold fractionalMomentIntegrand
    apply Continuous.div
    · exact (Real.continuous_rpow_const hα.le).comp continuous_abs
    · fun_prop
    · intro x
      positivity
  apply hc.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (g := fun x : ℝ => x ^ (α-2))
  · filter_upwards [] with x
    simp [Function.comp_def, fractionalMomentIntegrand]
  · refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hden : 0 < 1+x^2 := by positivity
    have hpos : 0 ≤ fractionalMomentIntegrand α x := by
      unfold fractionalMomentIntegrand
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul]
    unfold fractionalMomentIntegrand
    rw [abs_of_pos hx0, Real.rpow_sub hx0, Real.rpow_two]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (sq_pos_of_pos hx0)
      (by linarith)
  · exact (integrableAtFilter_rpow_atTop_iff).mpr (by linarith)

theorem fractionalMoment_nonneg (α : ℝ) : 0 ≤ fractionalMoment α := by
  apply integral_nonneg
  intro x
  unfold fractionalMomentIntegrand
  positivity

/-- Exact rescaling of the centered fractional Poisson kernel. -/
theorem fractional_kernel_rescale (α : ℝ) {η : ℝ} (hη : 0 < η) (u : ℝ) :
    kernel 0 η (η*u) * |η*u|^α =
      (η^α / η) * fractionalMomentIntegrand α u := by
  have hd : 0 < 1+u^2 := by positivity
  unfold kernel fractionalMomentIntegrand
  rw [abs_mul, abs_of_pos hη, Real.mul_rpow hη.le (abs_nonneg u)]
  field_simp
  <;> ring

theorem centered_fractional_kernel_integrable {α η : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    Integrable (fun x : ℝ => kernel 0 η x * |x|^α) := by
  apply (integrable_comp_mul_left_iff _ hη.ne').mp
  have h := (fractionalMoment_integrable hα hα1).const_mul (η^α/η)
  exact h.congr (Filter.Eventually.of_forall fun u => (fractional_kernel_rescale α hη u).symm)

theorem centered_fractional_kernel_integral (α : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ, kernel 0 η x * |x|^α) = η^α * fractionalMoment α := by
  have hs := Measure.integral_comp_mul_left (fun x : ℝ => kernel 0 η x * |x|^α) η
  simp_rw [fractional_kernel_rescale α hη] at hs
  rw [integral_const_mul] at hs
  simp only [abs_inv, abs_of_pos hη, smul_eq_mul] at hs
  field_simp [hη.ne'] at hs
  exact hs.symm

/-- The fractional moment centered at E has scale η^α exactly. -/
theorem translated_fractional_kernel_integral (α E : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ, kernel E η x * |x-E|^α) = η^α * fractionalMoment α := by
  have ht := integral_sub_right_eq_self (μ := volume)
    (fun x : ℝ => kernel 0 η x * |x|^α) E
  simpa only [kernel, sub_zero] using ht.trans (centered_fractional_kernel_integral α hη)

theorem translated_fractional_kernel_integrable {α η : ℝ} (E : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    Integrable (fun x : ℝ => kernel E η x * |x-E|^α) := by
  simpa only [kernel, sub_zero] using
    (centered_fractional_kernel_integrable hα hα1 hη).comp_sub_right E

theorem kernel_volume_integrable (E : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (kernel E η) := by
  have h0 : Integrable (kernel 0 η) := by
    apply (integrable_comp_mul_left_iff _ hη.ne').mp
    have h := integrable_inv_one_add_sq.const_mul (η⁻¹)
    convert h using 1
    ext u
    simpa [fractionalMomentIntegrand] using fractional_kernel_rescale 0 hη u
  simpa only [kernel, sub_zero] using h0.comp_sub_right E

theorem kernel_volume_integral (E : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ, kernel E η x) = Real.pi := by
  simpa [fractionalMoment, fractionalMomentIntegrand] using
    translated_fractional_kernel_integral 0 E hη

theorem fractional_triangle {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (E x : ℝ) :
    |x|^α ≤ |E|^α + |x-E|^α := by
  have ht : |x| ≤ |E|+|x-E| := by
    convert abs_add_le E (x-E) using 1 <;> ring
  exact (Real.rpow_le_rpow (abs_nonneg _) ht hα).trans
    (Real.rpow_add_le_add_rpow (abs_nonneg E) (abs_nonneg (x-E)) hα hα1)

theorem weighted_kernel_integrable {α η : ℝ} (E : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    Integrable (fun x : ℝ => kernel E η x * |x|^α) := by
  have hd := ((kernel_volume_integrable E hη).const_mul (|E|^α)).add
    (translated_fractional_kernel_integrable E hα hα1 hη)
  apply hd.mono' (by apply Measurable.aestronglyMeasurable; unfold kernel; fun_prop)
  filter_upwards [] with x
  have hk := kernel_nonneg (E := E) (t := x) hη.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (Real.rpow_nonneg (abs_nonneg x) α))]
  have h := mul_le_mul_of_nonneg_left (fractional_triangle hα.le hα1.le E x) hk
  change kernel E η x * |x|^α ≤ |E|^α * kernel E η x + kernel E η x * |x-E|^α
  nlinarith

/-- Uniform upper fractional Poisson scale. This includes the cusp upper bound
α=1/3 and the support-side edge upper bound α=1/2. -/
theorem weighted_kernel_upper {α η : ℝ} (E : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    (∫ x : ℝ, kernel E η x * |x|^α) ≤
      (Real.pi + fractionalMoment α) * (|E|+η)^α := by
  have hm := weighted_kernel_integrable E hα hα1 hη
  have hd := ((kernel_volume_integrable E hη).const_mul (|E|^α)).add
    (translated_fractional_kernel_integrable E hα hα1 hη)
  have hle : ∀ᵐ x : ℝ, kernel E η x * |x|^α ≤
      |E|^α * kernel E η x + kernel E η x * |x-E|^α := by
    filter_upwards [] with x
    have h := mul_le_mul_of_nonneg_left (fractional_triangle hα.le hα1.le E x)
      (kernel_nonneg (E := E) (t := x) hη.le)
    nlinarith
  have hi := integral_mono_ae hm hd hle
  simp only [Pi.add_apply] at hi
  rw [integral_add ((kernel_volume_integrable E hη).const_mul (|E|^α))
    (translated_fractional_kernel_integrable E hα hα1 hη), integral_const_mul,
    kernel_volume_integral E hη, translated_fractional_kernel_integral α E hη] at hi
  have hE : |E|^α ≤ (|E|+η)^α :=
    Real.rpow_le_rpow (abs_nonneg E) (le_add_of_nonneg_right hη.le) hα.le
  have hη' : η^α ≤ (|E|+η)^α :=
    Real.rpow_le_rpow hη.le (le_add_of_nonneg_left (abs_nonneg E)) hα.le
  have hM := fractionalMoment_nonneg α
  nlinarith [mul_le_mul_of_nonneg_right hE Real.pi_pos.le,
    mul_le_mul_of_nonneg_right hη' hM]

/-- Integrating a constant lower bound on a genuine interval witness. -/
theorem integral_lower_of_interval {f : ℝ → ℝ} {A : Set ℝ} {a b c : ℝ}
    (hi : IntegrableOn f A) (hn : ∀ x, 0 ≤ f x) (hab : a ≤ b)
    (hsub : Icc a b ⊆ A) (hlower : ∀ x ∈ Icc a b, c ≤ f x) :
    c * (b-a) ≤ ∫ x in A, f x := by
  have hloc := setIntegral_mono_on (integrable_const c) (hi.mono_set hsub)
    measurableSet_Icc hlower
  have hvol : (volume.restrict (Icc a b)).real univ = b-a := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using Real.volume_real_Icc_of_le hab
  rw [integral_const, smul_eq_mul, hvol] at hloc
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall fun x hx => hsub hx)
  have hloc' : c*(b-a) ≤ ∫ x in Icc a b, f x := by simpa only [mul_comm] using hloc
  exact hloc'.trans hmono

theorem kernel_lower_near {E η x : ℝ} (hη : 0 < η) (hnear : |x-E| ≤ 2*η) :
    (5*η)⁻¹ ≤ kernel E η x := by
  have hd : 0 < (x-E)^2+η^2 := by positivity
  have hsq := mul_self_le_mul_self (abs_nonneg (x-E)) hnear
  rw [← pow_two, sq_abs] at hsq
  unfold kernel
  rw [← one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < 5*η) hd).mpr
  nlinarith

/-- Lower fractional scale from an interval of width η. -/
theorem weighted_kernel_lower_of_interval {α η E q a : ℝ} {A : Set ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) (hq : 0 ≤ q)
    (hsub : Icc a (a+η) ⊆ A)
    (hnear : ∀ x ∈ Icc a (a+η), |x-E| ≤ 2*η)
    (hfar : ∀ x ∈ Icc a (a+η), q ≤ |x|) :
    q^α / 5 ≤ ∫ x in A, kernel E η x * |x|^α := by
  have hm := (weighted_kernel_integrable E hα hα1 hη).integrableOn (s := A)
  have hl : ∀ x ∈ Icc a (a+η), q^α/(5*η) ≤ kernel E η x * |x|^α := by
    intro x hx
    have hk := kernel_lower_near hη (hnear x hx)
    have hp := Real.rpow_le_rpow hq (hfar x hx) hα.le
    have h := mul_le_mul hk hp (Real.rpow_nonneg hq α)
      (kernel_nonneg (E := E) (t := x) hη.le)
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hi := integral_lower_of_interval hm
    (fun x => mul_nonneg (kernel_nonneg hη.le) (Real.rpow_nonneg (abs_nonneg x) α))
    (by linarith : a ≤ a+η) hsub hl
  have heq : q^α/(5*η) * (a+η-a) = q^α/5 := by
    field_simp
    <;> ring
  rw [heq] at hi
  exact hi

/-- Support-side edge lower scale, uniform even when κ and η are comparable.
The interval [κ+η,κ+2η] gives a single proof of all regimes. -/
theorem edge_support_lower {α κ η r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hκ : 0 ≤ κ) (hη : 0 < η)
    (hsmall : κ+2*η < r) :
    (κ+η)^α/5 ≤ ∫ x in Ioo 0 r, kernel κ η x * |x|^α := by
  apply weighted_kernel_lower_of_interval hα hα1 hη (by positivity : 0 ≤ κ+η)
    (a := κ+η)
  · intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro x hx
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x-κ)]
    linarith [hx.2]
  · intro x hx
    rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x)]
    exact hx.1

/-- Cusp lower scale on a symmetric local window. This is proved from an
explicit interval on the same side as E, for both signs of E. -/
theorem cusp_lower {α E η r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η)
    (hsmall : |E|+2*η < r) :
    (|E|+η)^α/5 ≤ ∫ x in Ioo (-r) r, kernel E η x * |x|^α := by
  by_cases hE : 0 ≤ E
  · have hsmall' : E+2*η < r := by simpa [abs_of_nonneg hE] using hsmall
    have he := edge_support_lower hα hα1 hE hη hsmall'
    have hm := setIntegral_mono_set
      ((weighted_kernel_integrable E hα hα1 hη).integrableOn (s := Ioo (-r) r))
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (kernel_nonneg hη.le) (Real.rpow_nonneg (abs_nonneg x) α))
      (Filter.Eventually.of_forall fun x (hx : x ∈ Ioo 0 r) =>
        (show x ∈ Ioo (-r) r from ⟨by linarith [abs_nonneg E, hx.1], hx.2⟩))
    simpa [abs_of_nonneg hE] using he.trans hm
  · have hE' : E ≤ 0 := le_of_not_ge hE
    rw [abs_of_nonpos hE'] at hsmall ⊢
    apply weighted_kernel_lower_of_interval hα hα1 hη (by linarith : 0 ≤ -E+η)
      (a := E-2*η)
    · intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · intro x hx
      rw [abs_of_nonpos (by linarith [hx.2] : x-E ≤ 0)]
      linarith [hx.1]
    · intro x hx
      rw [abs_of_nonpos (by linarith [hx.2] : x ≤ 0)]
      linarith [hx.2]

/-- Local upper scale on every measurable window, including one-sided edges
and symmetric cusps. -/
theorem local_weighted_kernel_upper {α η : ℝ} (E : ℝ) (A : Set ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    (∫ x in A, kernel E η x * |x|^α) ≤
      (Real.pi + fractionalMoment α) * (|E|+η)^α := by
  exact (setIntegral_le_integral (weighted_kernel_integrable E hα hα1 hη)
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (kernel_nonneg hη.le) (Real.rpow_nonneg (abs_nonneg x) α))).trans
    (weighted_kernel_upper E hα hα1 hη)

def gapMomentIntegrand (α x : ℝ) : ℝ := x^α/(1+x)^2
def gapMoment (α : ℝ) : ℝ := ∫ x in Ioi 0, gapMomentIntegrand α x

theorem gapMoment_integrable {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    IntegrableOn (gapMomentIntegrand α) (Ioi 0) := by
  apply ((fractionalMoment_integrable hα hα1).integrableOn (s := Ioi 0)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold gapMomentIntegrand; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  have hn : 0 ≤ gapMomentIntegrand α x := by unfold gapMomentIntegrand; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  unfold gapMomentIntegrand fractionalMomentIntegrand
  rw [abs_of_pos hx']
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx'.le α) (by positivity)
  nlinarith

theorem gapMoment_nonneg (α : ℝ) : 0 ≤ gapMoment α := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  unfold gapMomentIntegrand
  exact div_nonneg (Real.rpow_nonneg (le_of_lt hx) α) (sq_nonneg _)

theorem gap_kernel_rescale (α : ℝ) {q : ℝ} (hq : 0 < q) {u : ℝ} (hu : 0 < u) :
    (q*u)^α/(q*u+q)^2 = (q^α/q^2) * gapMomentIntegrand α u := by
  unfold gapMomentIntegrand
  rw [Real.mul_rpow hq.le hu.le]
  field_simp
  <;> ring

theorem gap_kernel_integrable {α q : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hq : 0 < q) :
    IntegrableOn (fun x : ℝ => x^α/(x+q)^2) (Ioi 0) := by
  have hs := integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => x^α/(x+q)^2) 0 hq
  simp only [mul_zero] at hs
  apply hs.mp
  exact ((gapMoment_integrable hα hα1).const_mul (q^α/q^2)).congr
    ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => (gap_kernel_rescale α hq hx).symm)

theorem gap_kernel_integral (α : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi 0, x^α/(x+q)^2) = q^α/q * gapMoment α := by
  have heq : (∫ x in Ioi 0, (q*x)^α/(q*x+q)^2) =
      (q^α/q^2) * gapMoment α := by
    unfold gapMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx => gap_kernel_rescale α hq hx
  rw [integral_comp_mul_left_Ioi (fun x : ℝ => x^α/(x+q)^2) 0 hq] at heq
  simp only [mul_zero, smul_eq_mul] at heq
  field_simp [hq.ne'] at heq ⊢
  nlinarith

/-- The elementary denominator comparison responsible for the gap-side scale. -/
theorem gap_kernel_upper_point {κ η x : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) (hx : 0 ≤ x) :
    kernel (-κ) η x ≤ 2*η/(x+(κ+η))^2 := by
  have hd : 0 < (x-(-κ))^2+η^2 := by positivity
  have hd' : 0 < (x+(κ+η))^2 := by positivity
  unfold kernel
  apply (div_le_div_iff₀ hd hd').mpr
  nlinarith [sq_nonneg (x+κ-η)]

/-- Gap-side upper scale, for every fractional exponent in (0,1). -/
theorem edge_gap_upper {α κ η r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hκ : 0 ≤ κ) (hη : 0 < η) :
    (∫ x in Ioo 0 r, kernel (-κ) η x * |x|^α) ≤
      2*η * ((κ+η)^α/(κ+η)) * gapMoment α := by
  have hq : 0 < κ+η := by positivity
  have hf := (weighted_kernel_integrable (-κ) hα hα1 hη).integrableOn (s := Ioo 0 r)
  have hg : IntegrableOn (fun x : ℝ => 2*η*(x^α/(x+(κ+η))^2)) (Ioi 0) :=
    (gap_kernel_integrable hα hα1 hq).const_mul (2*η)
  have hlocal := setIntegral_mono_on hf (hg.mono_set Ioo_subset_Ioi_self)
    measurableSet_Ioo (fun x (hx : x ∈ Ioo 0 r) => ?_)
  · have hmono := setIntegral_mono_set hg
      ((ae_restrict_mem measurableSet_Ioi).mono fun x (hx : 0 < x) => by positivity)
      (Filter.Eventually.of_forall fun x (hx : x ∈ Ioo 0 r) => hx.1)
    have h := hlocal.trans hmono
    rw [integral_const_mul, gap_kernel_integral α hq] at h
    convert h using 1 <;> ring
  · have hp := mul_le_mul_of_nonneg_right (gap_kernel_upper_point hκ hη hx.1.le)
      (Real.rpow_nonneg hx.1.le α)
    simpa [abs_of_pos hx.1, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hp

/-- Gap-side lower scale from the interval [q,2q], where q=κ+η. -/
theorem edge_gap_lower {α κ η r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hκ : 0 ≤ κ) (hη : 0 < η)
    (hsmall : 2*(κ+η) < r) :
    η*((κ+η)^α/(κ+η))/10 ≤ ∫ x in Ioo 0 r, kernel (-κ) η x * |x|^α := by
  let q := κ+η
  have hq : 0 < q := by dsimp [q]; positivity
  have hsub : Icc q (2*q) ⊆ Ioo 0 r := fun x hx =>
    ⟨hq.trans_le hx.1, lt_of_le_of_lt hx.2 hsmall⟩
  have hp : ∀ x ∈ Icc q (2*q), η*q^α/(10*q^2) ≤ kernel (-κ) η x * |x|^α := by
    intro x hx
    have hx0 : 0 < x := hq.trans_le hx.1
    have hd : 0 < (x-(-κ))^2+η^2 := by positivity
    have hdle : (x-(-κ))^2+η^2 ≤ 10*q^2 := by
      have ht : x+κ ≤ 3*q := by dsimp [q] at *; linarith [hx.2]
      have hh := mul_self_le_mul_self (by positivity : 0 ≤ x+κ) ht
      have heta : η ≤ q := by dsimp [q]; linarith
      have hh' := mul_self_le_mul_self hη.le heta
      nlinarith
    have hk : η/(10*q^2) ≤ kernel (-κ) η x :=
      div_le_div_of_nonneg_left hη.le hd hdle
    have hxpow := Real.rpow_le_rpow hq.le hx.1 hα.le
    have hm := mul_le_mul hk hxpow (Real.rpow_nonneg hq.le α)
      (kernel_nonneg (E := -κ) (t := x) hη.le)
    simpa [abs_of_pos hx0, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hm
  have hi := integral_lower_of_interval
    ((weighted_kernel_integrable (-κ) hα hα1 hη).integrableOn (s := Ioo 0 r))
    (fun x => mul_nonneg (kernel_nonneg hη.le) (Real.rpow_nonneg (abs_nonneg x) α))
    (by linarith : q ≤ 2*q) hsub hp
  convert hi using 1
  dsimp [q]
  field_simp
  <;> ring

end NonSymmetricDyson.Full.Poisson
