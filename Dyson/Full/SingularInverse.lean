import Dyson.Full.SingularLinear
import Dyson.Full.Deflation
import Dyson.Full.EuclideanInverse

/-! Local inverse estimates from the actual analytic Dyson curve. The
simple kernel and its nonzero opening are derived from the actual normalized
Perron data, then the internally verified deflation estimate is applied. -/

noncomputable section
open scoped Topology BigOperators
open Filter

namespace NonSymmetricDyson.Full.SingularLinear

variable {ι : Type*} [Fintype ι]

def stabilityCLM (S : Matrix ι ι ℝ) (m : ι → ℂ) :
    (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (InteriorStability.stabilityOperator S m).toContinuousLinearMap

@[simp] theorem stabilityCLM_apply (S : Matrix ι ι ℝ) (m u : ι → ℂ) :
    stabilityCLM S m u = InteriorStability.stabilityOperator S m u := rfl

theorem continuous_stabilityCLM (S : Matrix ι ι ℝ) : Continuous (stabilityCLM S) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  simp only [stabilityCLM_apply, InteriorStability.stabilityOperator_apply]
  fun_prop

def coordinateDivision (q : ι → ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.mul ℂ (ι → ℂ) (fun i => (q i)⁻¹)

@[simp] theorem coordinateDivision_apply (q x : ι → ℂ) (i : ι) :
    coordinateDivision q x i = x i / q i := by
  simp [coordinateDivision, div_eq_mul_inv, mul_comm]

/-- The actual original stability operator is diagonally similar to I-F
at a real boundary point. -/
theorem normalized_stability_identity
    (S : Matrix ι ι ℝ) (m q : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hq : ∀ i, q i ≠ 0) (hsq : ∀ i, m i ^ 2 = q i ^ 2)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (u : ι → ℂ) :
    coordinateDivision q (stabilityCLM S m u) =
      coordinateDivision q u - F (coordinateDivision q u) := by
  rw [hF]
  funext i
  simp only [coordinateDivision_apply, stabilityCLM_apply,
    InteriorStability.stabilityOperator_apply, Pi.sub_apply,
    DysonPaper.Algebra.scaledOperator, DysonPaper.Algebra.coordMul, Model.action_apply]
  have he : (∑ j, (S i j : ℂ) * (q j * (u j / q j))) = ∑ j, (S i j : ℂ) * u j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_cancel₀ _ (hq j)]
  rw [he, hsq i]
  field_simp [hq i]

/-- The required normalized left functional and simple kernel are obtained
from the normalized Perron data by the actual diagonal coordinate map. -/
theorem actual_singular_kernel_data
    (S : Matrix ι ι ℝ) (m q r : ι → ℂ)
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (hq : ∀ i, q i ≠ 0) (hsq : ∀ i, m i ^ 2 = q i ^ 2)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hnorm : ℓ r = 1) (hμ : ℓ q ≠ 0)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r) :
    ∃ φ : (ι → ℂ) →L[ℂ] ℂ,
      φ (fun i => q i*r i) = 1 ∧ φ (fun i => (m i)^2) ≠ 0 ∧
      (∀ x, φ (stabilityCLM S m x) = 0) ∧
      (∀ x, stabilityCLM S m x = 0 → x = φ x • (fun i => q i*r i)) := by
  let φ := ℓ.comp (coordinateDivision q)
  have hdiv (x : ι → ℂ) : φ x = ℓ (coordinateDivision q x) := rfl
  have hn : coordinateDivision q (fun i => q i*r i) = r := by
    funext i
    simp [hq i]
  have hb : coordinateDivision q (fun i => (m i)^2) = q := by
    funext i
    rw [coordinateDivision_apply, hsq i]
    field_simp [hq i]
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · rw [hdiv, hn, hnorm]
  · rw [hdiv, hb]
    exact hμ
  · intro x
    rw [hdiv, normalized_stability_identity S m q F hq hsq hF, map_sub, hlF, sub_self]
  · intro x hx
    have he := normalized_stability_identity S m q F hq hsq hF x
    rw [hx, map_zero] at he
    have hfix : F (coordinateDivision q x) = coordinateDivision q x :=
      (sub_eq_zero.mp he.symm).symm
    have hs := hsimple (coordinateDivision q x) hfix
    funext i
    have hh := congrFun hs i
    simp only [coordinateDivision_apply, Pi.smul_apply, smul_eq_mul] at hh
    have hmul := (div_eq_iff (hq i)).mp hh
    change x i = φ x * (q i*r i)
    rw [hdiv]
    linear_combination hmul

/-- The monomial chart turns the exact differentiated Dyson equation into
an inverse bound of order |s|^{1-k}, in the actual Euclidean operator norm. -/
theorem monomial_curve_inverse [Nonempty ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (M : ℂ → ι → ℂ) (hMa : AnalyticAt ℂ M 0)
    (c : ℂ) (hc : c ≠ 0) (k : ℕ) (hk : 2 ≤ k)
    (hsol : ∀ᶠ s in 𝓝 (0 : ℂ), PolynomialDyson.IsPolynomialSolution S a
      ((τ : ℂ)+c*s^k) (M s))
    (φ : (ι → ℂ) →L[ℂ] ℂ)
    (hnorm : φ (deriv M 0) = 1) (hopen : φ (fun i => (M 0 i)^2) ≠ 0)
    (hleft : ∀ x, φ (stabilityCLM S (M 0) x) = 0)
    (hsimple : ∀ x, stabilityCLM S (M 0) x = 0 → x = φ x • deriv M 0) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ ∀ᶠ s in 𝓝 (0 : ℂ),
      ∀ hz : 0 < ((τ : ℂ)+c*s^k).im,
      ∀ hm : BasicEstimates.IsUpperSolution (M s),
      ∀ heq : BasicEstimates.IsDysonSolution S a ((τ : ℂ)+c*s^k) (M s),
      c₀/‖s‖^(k-1) ≤ ‖EuclideanInverse.stabilityInverse S a
        ((τ : ℂ)+c*s^k) (M s) hS hz hm heq‖ ∧
      ‖EuclideanInverse.stabilityInverse S a
        ((τ : ℂ)+c*s^k) (M s) hS hz hm heq‖ ≤ C₀/‖s‖^(k-1) := by
  let v : ℂ → ι → ℂ := deriv M
  let b : ℂ → ι → ℂ := fun s i => (M s i)^2
  let ω : ℂ → ℂ := fun s => c*(k : ℂ)*s^(k-1)
  have hv : ContinuousAt v 0 := hMa.deriv.continuousAt
  have hb : ContinuousAt b 0 := by
    apply continuousAt_pi.mpr
    intro i
    exact ((continuousAt_pi.mp hMa.continuousAt) i).pow 2
  have hL : ContinuousAt (fun s => stabilityCLM S (M s)) 0 :=
    (continuous_stabilityCLM S).continuousAt.comp hMa.continuousAt
  obtain ⟨C, hC, hbound⟩ := Deflation.local_linear_opening_bound
    (0 : ℂ) (fun s => stabilityCLM S (M s)) v b φ hL hv hb hnorm hopen hleft hsimple
  have hv0 : v 0 ≠ 0 := by
    intro he
    change φ (v 0) = 1 at hnorm
    rw [he, map_zero] at hnorm
    exact zero_ne_one hnorm
  let A : ℝ := ‖v 0‖/2
  let B : ℝ := Real.sqrt (Fintype.card ι)*(1+‖b 0‖)
  let D : ℝ := ‖c‖*(k : ℝ)
  have hcard : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hA : 0 < A := by dsimp [A]; exact half_pos (norm_pos_iff.mpr hv0)
  have hB : 0 < B := by dsimp [B]; positivity
  have hk0 : 0 < k := by omega
  have hD : 0 < D := mul_pos (norm_pos_iff.mpr hc) (by exact_mod_cast hk0)
  have hω : Continuous ω := by dsimp [ω]; fun_prop
  have hω0 : ω 0 = 0 := by simp [ω, show k-1 ≠ 0 by omega]
  have hωsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖ω s‖ ≤ 1 :=
    hω.continuousAt.norm.tendsto.eventually_le_const (by rw [hω0]; norm_num)
  have hvlarge : ∀ᶠ s in 𝓝 (0 : ℂ), A ≤ ‖v s‖ :=
    hv.norm.tendsto.eventually_const_le (by dsimp [A]; linarith [norm_pos_iff.mpr hv0])
  have hbsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖b s‖ ≤ 1+‖b 0‖ :=
    hb.norm.tendsto.eventually_le_const (by linarith)
  refine ⟨(A/B)/D, (Real.sqrt (Fintype.card ι)*C)/D,
    div_pos (div_pos hA hB) hD, div_pos (mul_pos hcard hC) hD, ?_⟩
  filter_upwards [hbound, hωsmall, hvlarge, hbsmall, hMa.eventually_analyticAt,
    eventually_eventually_nhds.mpr hsol] with s hs hωs hvs hbs has hnear
  intro hz hm heq
  have hs0 : s ≠ 0 := by intro he; simp [he, hk0.ne'] at hz
  have hωne : ω s ≠ 0 := mul_ne_zero (mul_ne_zero hc (by exact_mod_cast hk0.ne')) (pow_ne_zero _ hs0)
  have hid : stabilityCLM S (M s) (v s) = ω s • b s := by
    have hzderiv : HasDerivAt (fun t : ℂ => (τ : ℂ)+c*t^k) (ω s) s := by
      simpa [ω, mul_assoc] using ((hasDerivAt_id s).pow k).const_mul c |>.const_add (τ : ℂ)
    exact dyson_curve_derivative S a _ M s (ω s) (v s) hzderiv
      has.differentiableAt.hasDerivAt hnear
  have hωnorm : ‖ω s‖ = D*‖s‖^(k-1) := by simp [ω, D, norm_mul, norm_pow]
  constructor
  · have hl := EuclideanInverse.stability_inverse_lower S a _ (M s) hS hz hm heq
      (v s) (b s) (ω s) hωne A B hA hB
      (hvs.trans (Norms.sup_le_euclidean _))
      ((Norms.euclidean_le_sqrt_card_mul_sup _).trans (mul_le_mul_of_nonneg_left hbs hcard.le)) hid
    rw [hωnorm] at hl
    convert hl using 1 <;> dsimp [D] <;> ring
  · have hu := EuclideanInverse.stability_inverse_upper S a _ (M s) hS hz hm heq
      (C/‖ω s‖) (by positivity) (hs (ω s) hωne hωs hid)
    rw [hωnorm] at hu
    convert hu using 1 <;> dsimp [D] <;> ring

/-- The tangent of a degree at least two solution curve lies in the
actual boundary stability kernel. -/
theorem monomial_curve_tangent_kernel
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ)
    (M : ℂ → ι → ℂ) (hMa : AnalyticAt ℂ M 0)
    (c : ℂ) (k : ℕ) (hk : 2 ≤ k)
    (hsol : ∀ᶠ s in 𝓝 (0 : ℂ), PolynomialDyson.IsPolynomialSolution S a
      ((τ : ℂ)+c*s^k) (M s)) : stabilityCLM S (M 0) (deriv M 0) = 0 := by
  have hzderiv : HasDerivAt (fun t : ℂ => (τ : ℂ)+c*t^k) 0 0 := by
    simpa [show k-1 ≠ 0 by omega] using
      ((hasDerivAt_id (0 : ℂ)).pow k).const_mul c |>.const_add (τ : ℂ)
  have hh := dyson_curve_derivative S a _ M 0 0 (deriv M 0) hzderiv
    hMa.differentiableAt.hasDerivAt hsol
  simpa using hh

/-- Renormalize the fixed left functional by the actual tangent. -/
theorem renormalize_kernel_direction
    (L : (ι → ℂ) →L[ℂ] (ι → ℂ)) (φ₀ : (ι → ℂ) →L[ℂ] ℂ)
    (r v b : ι → ℂ) (hleft : ∀ x, φ₀ (L x) = 0)
    (hsimple : ∀ x, L x = 0 → x = φ₀ x • r)
    (hv : L v = 0) (hφv : φ₀ v ≠ 0) (hφb : φ₀ b ≠ 0) :
    ∃ φ : (ι → ℂ) →L[ℂ] ℂ, φ v = 1 ∧ φ b ≠ 0 ∧
      (∀ x, φ (L x) = 0) ∧ (∀ x, L x = 0 → x = φ x • v) := by
  let φ : (ι → ℂ) →L[ℂ] ℂ := (φ₀ v)⁻¹ • φ₀
  have hφ (x) : φ x = (φ₀ v)⁻¹ * φ₀ x := rfl
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · rw [hφ, inv_mul_cancel₀ hφv]
  · rw [hφ]
    exact mul_ne_zero (inv_ne_zero hφv) hφb
  · intro x
    rw [hφ, hleft, mul_zero]
  · intro x hx
    have hc : ((φ₀ v)⁻¹ * φ₀ x) * φ₀ v = φ₀ x := by field_simp
    have he : φ x • v = φ₀ x • r := by
      calc
        φ x • v = ((φ₀ v)⁻¹ * φ₀ x) • (φ₀ v • r) := by
          rw [hφ]
          exact congrArg (fun w => ((φ₀ v)⁻¹ * φ₀ x) • w) (hsimple v hv)
        _ = φ₀ x • r := by rw [smul_smul, hc]
    exact (hsimple x hx).trans he.symm

end NonSymmetricDyson.Full.SingularLinear
