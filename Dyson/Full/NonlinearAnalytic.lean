import Mathlib

/-!+The analytic input in this file is the ordinary local analytic implicit
function theorem. Its statement is universally quantified over analytic maps,
and does not mention the Dyson equation or stability estimates. Its application
to the displayed polynomial is verified below.
-/

noncomputable section
open scoped Topology

namespace NonSymmetricDyson.Full.Nonlinear

/-- The standard analytic implicit function theorem, specialized only to an
identity partial derivative. This is a precise external mathematical argument,
not a nonlinear stability assumption. -/
def AnalyticImplicitFunctionPrinciple
    (E P : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P] : Prop :=
  ∀ H : E × P → E, AnalyticAt ℂ H 0 → H 0 = 0 →
    HasFDerivAt (fun w => H (w, 0)) (ContinuousLinearMap.id ℂ E) 0 →
    ∃ W : P → E, AnalyticAt ℂ W 0 ∧ W 0 = 0 ∧
      ∃ εw > 0, ∃ εp > 0,
        (∀ p, ‖p‖ < εp → H (W p, p) = 0 ∧ ‖W p‖ < εw) ∧
        (∀ w p, ‖w‖ < εw → ‖p‖ < εp → (H (w, p) = 0 ↔ w = W p))

variable {ι : Type*} [Fintype ι]

/-- Actual finite-vector quadratic nonlinearity, with componentwise products. -/
def quadraticNonlinearity (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (p q h ξ : ι → ℂ) : ι → ℂ :=
  p * h * F h + q * (1 + p * h) * ξ

/-- Stable equation whose partial derivative is the identity. -/
def stableResidual (F K : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (p q r : ι → ℂ) (v : (ι → ℂ) × (ℂ × (ι → ℂ))) : ι → ℂ :=
  v.1 - K (quadraticNonlinearity F p q (v.2.1 • r + v.1) v.2.2)

theorem quadraticNonlinearity_analytic
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q : ι → ℂ)
    (x : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun v : (ι → ℂ) × (ι → ℂ) =>
      quadraticNonlinearity F p q v.1 v.2) x := by
  have h₁ : AnalyticAt ℂ (fun v : (ι → ℂ) × (ι → ℂ) => v.1) x := analyticAt_fst
  have h₂ : AnalyticAt ℂ (fun v : (ι → ℂ) × (ι → ℂ) => v.2) x := analyticAt_snd
  exact ((analyticAt_const.mul h₁).mul ((F.analyticAt _).comp h₁)).add
    ((analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul h₁))).mul h₂)

theorem stableResidual_analytic
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ)
    (x : (ι → ℂ) × (ℂ × (ι → ℂ))) :
    AnalyticAt ℂ (stableResidual F K p q r) x := by
  have hw : AnalyticAt ℂ (fun v : (ι → ℂ) × (ℂ × (ι → ℂ)) => v.1) x := analyticAt_fst
  have hθ : AnalyticAt ℂ (fun v : (ι → ℂ) × (ℂ × (ι → ℂ)) => v.2.1) x :=
    analyticAt_fst.comp analyticAt_snd
  have hξ : AnalyticAt ℂ (fun v : (ι → ℂ) × (ℂ × (ι → ℂ)) => v.2.2) x :=
    analyticAt_snd.comp analyticAt_snd
  have hh : AnalyticAt ℂ (fun v : (ι → ℂ) × (ℂ × (ι → ℂ)) =>
      v.2.1 • r + v.1) x := (hθ.smul (analyticAt_const (v := r))).add hw
  have hN := (quadraticNonlinearity_analytic F p q _).comp (hh.prod hξ)
  exact hw.sub ((K.analyticAt _).comp hN)

@[simp] theorem stableResidual_zero
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ) :
    stableResidual F K p q r 0 = 0 := by
  simp [stableResidual, quadraticNonlinearity]

/-- The invertibility hypothesis of the analytic IFT is checked for the
actual polynomial, rather than supplied as a Dyson-specific assumption. -/
theorem stableResidual_partial_derivative
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ) :
    HasFDerivAt (fun w => stableResidual F K p q r (w, 0))
      (ContinuousLinearMap.id ℂ (ι → ℂ)) 0 := by
  have hi := hasFDerivAt_id (𝕜 := ℂ) (0 : ι → ℂ)
  have hp := hasFDerivAt_const (𝕜 := ℂ) p (0 : ι → ℂ)
  have hquad : HasFDerivAt (fun w : ι → ℂ => p * w * F w)
      (0 : (ι → ℂ) →L[ℂ] (ι → ℂ)) 0 := by
    simpa using (hp.mul hi).mul (F.hasFDerivAt)
  have h := hi.sub ((K.hasFDerivAt).comp 0 hquad)
  simpa [stableResidual, quadraticNonlinearity] using h

/-- Application of the general analytic implicit theorem: the stable
coordinate exists, is analytic, and is uniquely characterized by the actual
polynomial fixed-point equation. -/
theorem analytic_stable_elimination
    (ift : AnalyticImplicitFunctionPrinciple (ι → ℂ) (ℂ × (ι → ℂ)))
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ) :
    ∃ W : ℂ × (ι → ℂ) → (ι → ℂ), AnalyticAt ℂ W 0 ∧ W 0 = 0 ∧
      ∃ εw > 0, ∃ εp > 0,
        (∀ v, ‖v‖ < εp →
          W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2) ∧
          ‖W v‖ < εw) ∧
        (∀ w v, ‖w‖ < εw → ‖v‖ < εp →
          (w = K (quadraticNonlinearity F p q (v.1 • r + w) v.2) ↔ w = W v)) := by
  obtain ⟨W, hWa, hW0, εw, hεw, εp, hεp, hW, huniq⟩ :=
    ift (stableResidual F K p q r) (stableResidual_analytic F K p q r 0)
      (stableResidual_zero F K p q r) (stableResidual_partial_derivative F K p q r)
  refine ⟨W, hWa, hW0, εw, hεw, εp, hεp, ?_, ?_⟩
  · intro v hv
    exact ⟨sub_eq_zero.mp (hW v hv).1, (hW v hv).2⟩
  · intro w v hw hv
    simpa only [stableResidual, sub_eq_zero] using huniq w v hw hv

/-- Every fixed point constructed above belongs to the stable complement. -/
theorem stable_fixed_point_in_kernel
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hℓK : ∀ x, ℓ (K x) = 0)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ)) : ℓ w = 0 := by
  rw [hw]
  exact hℓK _

/-- Quantitative polynomial bound used in the contraction and remainder
arguments. The norm is the actual supremum norm of finite complex vectors. -/
theorem quadraticNonlinearity_norm_bound
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q h ξ : ι → ℂ) :
    ‖quadraticNonlinearity F p q h ξ‖ ≤
      ‖p‖ * ‖F‖ * ‖h‖ ^ 2 + ‖q‖ * (1 + ‖p‖ * ‖h‖) * ‖ξ‖ := by
  have hF : ‖F h‖ ≤ ‖F‖ * ‖h‖ := F.le_opNorm h
  have hph : ‖p * h‖ ≤ ‖p‖ * ‖h‖ := norm_mul_le p h
  have hone : ‖(1 : ι → ℂ) + p * h‖ ≤ 1 + ‖p‖ * ‖h‖ := by
    calc
      _ ≤ ‖(1 : ι → ℂ)‖ + ‖p * h‖ := norm_add_le _ _
      _ ≤ _ := add_le_add
        ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)) hph
  calc
    _ ≤ ‖p * h * F h‖ + ‖q * (1 + p * h) * ξ‖ := norm_add_le _ _
    _ ≤ (‖p‖ * ‖h‖) * (‖F‖ * ‖h‖) +
        (‖q‖ * (1 + ‖p‖ * ‖h‖)) * ‖ξ‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans
          (mul_le_mul hph hF (norm_nonneg _) (by positivity))
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hone (norm_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

/-- A fixed point has the quadratic size bound needed for Taylor expansion.
Its smallness condition is precisely the coefficient that is absorbed. -/
theorem stable_fixed_point_size
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ))
    (hlocal : ‖θ • r + w‖ ≤ 1)
    (hsmall : 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖w‖ ≤ 1) :
    ‖w‖ ≤ 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2 * ‖θ‖ ^ 2 +
      2 * ‖K‖ * ‖q‖ * (1 + ‖p‖) * ‖ξ‖ := by
  have hnorm : ‖θ • r + w‖ ≤ ‖θ‖ * ‖r‖ + ‖w‖ := by
    simpa only [norm_smul] using norm_add_le (θ • r) w
  have hsq : ‖θ • r + w‖ ^ 2 ≤ 2 * ‖θ‖ ^ 2 * ‖r‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖θ‖ * ‖r‖ - ‖w‖), norm_nonneg (θ • r + w)]
  have hforce : 1 + ‖p‖ * ‖θ • r + w‖ ≤ 1 + ‖p‖ := by
    nlinarith [norm_nonneg p]
  have hineq : ‖w‖ ≤
      2 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2 * ‖θ‖ ^ 2 +
      2 * (‖K‖ * ‖p‖ * ‖F‖) * ‖w‖ ^ 2 +
      ‖K‖ * ‖q‖ * (1 + ‖p‖) * ‖ξ‖ := by
    calc
      ‖w‖ = ‖K (quadraticNonlinearity F p q (θ • r + w) ξ)‖ := congrArg norm hw
      _ ≤ ‖K‖ * ‖quadraticNonlinearity F p q (θ • r + w) ξ‖ := K.le_opNorm _
      _ ≤ ‖K‖ * (‖p‖ * ‖F‖ * ‖θ • r + w‖ ^ 2 +
          ‖q‖ * (1 + ‖p‖ * ‖θ • r + w‖) * ‖ξ‖) :=
        mul_le_mul_of_nonneg_left (quadraticNonlinearity_norm_bound F p q _ ξ) (norm_nonneg _)
      _ ≤ ‖K‖ * (‖p‖ * ‖F‖ * (2 * ‖θ‖ ^ 2 * ‖r‖ ^ 2 + 2 * ‖w‖ ^ 2) +
          ‖q‖ * (1 + ‖p‖) * ‖ξ‖) := by gcongr
      _ = _ := by ring
  have habs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg w)
  nlinarith

/-- Exact second-order stable-coordinate expansion. This identity computes
the Taylor coefficients without assuming any Dyson-specific expansion. -/
theorem stable_fixed_point_remainder_identity
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hFr : F r = r)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ)) :
    w - θ ^ 2 • K (p * r * r) - K (q * ξ) =
      K (θ • (p * r * F w + p * w * r) + p * w * F w +
        q * p * (θ • r + w) * ξ) := by
  calc
    _ = K (quadraticNonlinearity F p q (θ • r + w) ξ -
        θ ^ 2 • (p * r * r) - q * ξ) := by
      rw [map_sub, map_sub, map_smul]
      rw [← hw]
    _ = _ := by
      congr 1
      simp only [quadraticNonlinearity, map_add, map_smul, hFr]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply,
        Pi.smul_apply, smul_eq_mul]
      ring

/-- The displayed remainder is controlled by quadratic and mixed terms
before the size estimate for `w` is substituted. -/
theorem stable_fixed_point_remainder_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hFr : F r = r)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ)) :
    ‖w - θ ^ 2 • K (p * r * r) - K (q * ξ)‖ ≤
      ‖K‖ * (‖θ‖ * (‖p‖ * ‖r‖ * ‖F‖ * ‖w‖ + ‖p‖ * ‖w‖ * ‖r‖) +
        ‖p‖ * ‖w‖ * ‖F‖ * ‖w‖ +
        ‖q‖ * ‖p‖ * (‖θ‖ * ‖r‖ + ‖w‖) * ‖ξ‖) := by
  rw [stable_fixed_point_remainder_identity F K p q r w ξ θ hFr hw]
  apply (K.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖θ • (p * r * F w + p * w * r)‖ + ‖p * w * F w‖ +
        ‖q * p * (θ • r + w) * ξ‖ := (norm_add_le _ _).trans
      (add_le_add_right (norm_add_le _ _) _)
    _ ≤ _ := by
      rw [norm_smul]
      have hF := F.le_opNorm w
      have hsum : ‖θ • r + w‖ ≤ ‖θ‖ * ‖r‖ + ‖w‖ := by
        simpa only [norm_smul] using norm_add_le (θ • r) w
      have h₁ : ‖p * r * F w‖ ≤ ‖p‖ * ‖r‖ * ‖F‖ * ‖w‖ := by
        calc
          _ ≤ (‖p‖ * ‖r‖) * (‖F‖ * ‖w‖) :=
            (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hF
              (norm_nonneg _) (by positivity))
          _ = _ := by ring
      have h₂ : ‖p * w * r‖ ≤ ‖p‖ * ‖w‖ * ‖r‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      have h₃ : ‖p * w * F w‖ ≤ ‖p‖ * ‖w‖ * ‖F‖ * ‖w‖ := by
        calc
          _ ≤ (‖p‖ * ‖w‖) * (‖F‖ * ‖w‖) :=
            (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hF
              (norm_nonneg _) (by positivity))
          _ = _ := by ring
      have h₄ : ‖q * p * (θ • r + w) * ξ‖ ≤
          ‖q‖ * ‖p‖ * (‖θ‖ * ‖r‖ + ‖w‖) * ‖ξ‖ := by
        apply (norm_mul_le _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hsum
          (norm_nonneg _) (by positivity))
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂))
          (norm_nonneg _)) h₃) h₄

/-- Exact scalar coefficient calculation for the polynomial reduction.
Writing `e = w - θ² A` keeps every term of the remainder explicit. -/
theorem scalar_reduction_coefficient_identity
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r A w ξ : ι → ℂ) (θ : ℂ) (hFr : F r = r) :
    let e := w - θ ^ 2 • A
    ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) -
      θ ^ 2 * ℓ (p * r * r) - θ ^ 3 * ℓ (p * r * (F A + A)) - ℓ (q * ξ) =
      ℓ (θ • (p * r * F e + p * e * r) + p * w * F w +
        q * p * (θ • r + w) * ξ) := by
  dsimp
  have hid : quadraticNonlinearity F p q (θ • r + w) ξ -
      θ ^ 2 • (p * r * r) - θ ^ 3 • (p * r * (F A + A)) - q * ξ =
      θ • (p * r * F (w - θ ^ 2 • A) + p * (w - θ ^ 2 • A) * r) +
        p * w * F w + q * p * (θ • r + w) * ξ := by
    simp only [quadraticNonlinearity, map_add, map_sub, map_smul, hFr]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have h := congrArg ℓ hid
  simpa only [map_sub, map_smul, smul_eq_mul] using h

/-- A scalar quadratic/cubic equation with a controlled Taylor remainder
has the rough power bound. This elementary absorption is independent of root
selection, which is proved in `NonlinearRoots`. -/
theorem rough_scalar_power_bound
    (γ θ a R : ℂ) (k : ℕ) (C X : ℝ) (hγ : γ ≠ 0)
    (hX : 0 ≤ X) (hC : 0 ≤ C)
    (heq : γ * θ ^ k + a + R = 0)
    (ha : ‖a‖ ≤ C * X)
    (hR : ‖R‖ ≤ ‖γ‖ / 2 * ‖θ‖ ^ k + C * X) :
    ‖θ‖ ^ k ≤ (4 * C / ‖γ‖) * X := by
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have he : γ * θ ^ k = -(a + R) := by linear_combination heq
  have hb : ‖γ‖ * ‖θ‖ ^ k ≤ C * X + (‖γ‖ / 2 * ‖θ‖ ^ k + C * X) := by
    calc
      _ = ‖γ * θ ^ k‖ := by rw [norm_mul, norm_pow]
      _ = ‖a + R‖ := by rw [he, norm_neg]
      _ ≤ ‖a‖ + ‖R‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ha hR
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hγpos).mpr
  nlinarith

private theorem triple_product_norm_bound (a b c : ι → ℂ) :
    ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ :=
  (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-- The derivative-size estimate is obtained from an exact difference
identity for the polynomial, so no local Lipschitz conclusion is assumed. -/
theorem quadraticNonlinearity_difference_bound
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q h h' ξ ξ' : ι → ℂ) :
    ‖quadraticNonlinearity F p q h ξ - quadraticNonlinearity F p q h' ξ'‖ ≤
      (‖p‖ * ‖F‖ * (‖h‖ + ‖h'‖) + ‖q‖ * ‖p‖ * ‖ξ‖) * ‖h - h'‖ +
      ‖q‖ * (1 + ‖p‖ * ‖h'‖) * ‖ξ - ξ'‖ := by
  have heq : quadraticNonlinearity F p q h ξ - quadraticNonlinearity F p q h' ξ' =
      p * (h - h') * F h + p * h' * F (h - h') +
      q * p * (h - h') * ξ + q * (1 + p * h') * (ξ - ξ') := by
    simp only [quadraticNonlinearity, map_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply]
    ring
  have h₁ : ‖p * (h - h') * F h‖ ≤ ‖p‖ * ‖h - h'‖ * (‖F‖ * ‖h‖) :=
    (triple_product_norm_bound _ _ _).trans
      (mul_le_mul_of_nonneg_left (F.le_opNorm h) (by positivity))
  have h₂ : ‖p * h' * F (h - h')‖ ≤ ‖p‖ * ‖h'‖ * (‖F‖ * ‖h - h'‖) :=
    (triple_product_norm_bound _ _ _).trans
      (mul_le_mul_of_nonneg_left (F.le_opNorm _) (by positivity))
  have h₃ : ‖q * p * (h - h') * ξ‖ ≤ ‖q‖ * ‖p‖ * ‖h - h'‖ * ‖ξ‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (triple_product_norm_bound _ _ _) (norm_nonneg _))
  have hone : ‖(1 : ι → ℂ) + p * h'‖ ≤ 1 + ‖p‖ * ‖h'‖ := by
    apply (norm_add_le _ _).trans
    exact add_le_add
      ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)) (norm_mul_le _ _)
  have h₄ : ‖q * (1 + p * h') * (ξ - ξ')‖ ≤
      ‖q‖ * (1 + ‖p‖ * ‖h'‖) * ‖ξ - ξ'‖ :=
    (triple_product_norm_bound _ _ _).trans (by gcongr)
  rw [heq]
  calc
    _ ≤ ‖p * (h - h') * F h‖ + ‖p * h' * F (h - h')‖ +
        ‖q * p * (h - h') * ξ‖ + ‖q * (1 + p * h') * (ξ - ξ')‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add_right
      apply (norm_add_le _ _).trans
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ ‖p‖ * ‖h - h'‖ * (‖F‖ * ‖h‖) + ‖p‖ * ‖h'‖ * (‖F‖ * ‖h - h'‖) +
        ‖q‖ * ‖p‖ * ‖h - h'‖ * ‖ξ‖ + ‖q‖ * (1 + ‖p‖ * ‖h'‖) * ‖ξ - ξ'‖ :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = _ := by ring

/-- A quantitative stable-coordinate comparison derived directly from the
two fixed-point equations. It supplies the reconstruction estimate needed
after branch selection. -/
theorem stable_fixed_point_difference_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (p q r w w' ξ ξ' : ι → ℂ) (θ θ' : ℂ)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ))
    (hw' : w' = K (quadraticNonlinearity F p q (θ' • r + w') ξ'))
    (hsmall : ‖K‖ * (‖p‖ * ‖F‖ * (‖θ • r + w‖ + ‖θ' • r + w'‖) +
      ‖q‖ * ‖p‖ * ‖ξ‖) ≤ 1 / 2) :
    ‖w - w'‖ ≤ ‖r‖ * ‖θ - θ'‖ +
      2 * ‖K‖ * ‖q‖ * (1 + ‖p‖ * ‖θ' • r + w'‖) * ‖ξ - ξ'‖ := by
  let a := ‖p‖ * ‖F‖ * (‖θ • r + w‖ + ‖θ' • r + w'‖) + ‖q‖ * ‖p‖ * ‖ξ‖
  let b := ‖q‖ * (1 + ‖p‖ * ‖θ' • r + w'‖)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hdisp : ‖(θ • r + w) - (θ' • r + w')‖ ≤ ‖θ - θ'‖ * ‖r‖ + ‖w - w'‖ := by
    have he : (θ • r + w) - (θ' • r + w') = (θ - θ') • r + (w - w') := by
      simp only [sub_smul]
      abel
    rw [he]
    simpa only [norm_smul] using norm_add_le ((θ - θ') • r) (w - w')
  have hineq : ‖w - w'‖ ≤ ‖K‖ * a * (‖θ - θ'‖ * ‖r‖ + ‖w - w'‖) +
      ‖K‖ * b * ‖ξ - ξ'‖ := by
    calc
      _ = ‖K (quadraticNonlinearity F p q (θ • r + w) ξ -
          quadraticNonlinearity F p q (θ' • r + w') ξ')‖ := by rw [map_sub, ← hw, ← hw']
      _ ≤ ‖K‖ * ‖quadraticNonlinearity F p q (θ • r + w) ξ -
          quadraticNonlinearity F p q (θ' • r + w') ξ'‖ := K.le_opNorm _
      _ ≤ ‖K‖ * (a * ‖(θ • r + w) - (θ' • r + w')‖ + b * ‖ξ - ξ'‖) :=
        mul_le_mul_of_nonneg_left (quadraticNonlinearity_difference_bound F p q _ _ ξ ξ')
          (norm_nonneg _)
      _ ≤ ‖K‖ * (a * (‖θ - θ'‖ * ‖r‖ + ‖w - w'‖) + b * ‖ξ - ξ'‖) := by gcongr
      _ = _ := by ring
  have hsmall' : ‖K‖ * a ≤ 1 / 2 := hsmall
  have habs := mul_le_mul_of_nonneg_right hsmall'
    (show 0 ≤ ‖θ - θ'‖ * ‖r‖ + ‖w - w'‖ by positivity)
  dsimp [b] at hineq
  nlinarith

/-- The analytic elimination has a uniform quadratic size estimate on an
actual neighborhood. The neighborhood is chosen using continuity at the
origin; the bound itself follows from the proved polynomial absorption. -/
theorem analytic_stable_elimination_with_size
    (ift : AnalyticImplicitFunctionPrinciple (ι → ℂ) (ℂ × (ι → ℂ)))
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ) :
    ∃ W : ℂ × (ι → ℂ) → (ι → ℂ), AnalyticAt ℂ W 0 ∧ W 0 = 0 ∧
      ∃ ε > 0, ∃ C > 0, ∀ v, ‖v‖ < ε →
        W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2) ∧
        ‖W v‖ ≤ C * (‖v.1‖ ^ 2 + ‖v.2‖) := by
  obtain ⟨W, hWa, hW0, εw, hεw, εp, hεp, hW, huniq⟩ :=
    analytic_stable_elimination ift F K p q r
  have hcont : ContinuousAt (fun v : ℂ × (ι → ℂ) => ‖v.1 • r + W v‖) 0 :=
    ((continuousAt_fst.smul continuousAt_const).add hWa.continuousAt).norm
  have hcsmall : ContinuousAt (fun v : ℂ × (ι → ℂ) =>
      4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W v‖) 0 :=
    continuousAt_const.mul hWa.continuousAt.norm
  have hevent : ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 0,
      ‖v‖ < εp ∧ ‖v.1 • r + W v‖ < 1 ∧
        4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W v‖ < 1 := by
    have h₁ : ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 0, ‖v‖ < εp :=
      continuousAt_id.norm.eventually_lt continuousAt_const (by simpa using hεp)
    have h₂ := hcont.eventually_lt continuousAt_const
      (show ‖(0 : ℂ × (ι → ℂ)).1 • r + W 0‖ < 1 by simp [hW0])
    have h₃ := hcsmall.eventually_lt continuousAt_const
      (show 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W 0‖ < 1 by simp [hW0])
    filter_upwards [h₁, h₂, h₃] with v h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let a := 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2
  let b := 2 * ‖K‖ * ‖q‖ * (1 + ‖p‖)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨W, hWa, hW0, ε, hε, 1 + a + b, by positivity, ?_⟩
  intro v hv
  have hv' := hball (by simpa using hv)
  have heq := (hW v hv'.1).1
  refine ⟨heq, ?_⟩
  have hbound : ‖W v‖ ≤ a * ‖v.1‖ ^ 2 + b * ‖v.2‖ :=
    stable_fixed_point_size F K p q r (W v) v.2 v.1 heq hv'.2.1.le hv'.2.2.le
  have hx : 0 ≤ ‖v.1‖ ^ 2 := sq_nonneg _
  have hy : 0 ≤ ‖v.2‖ := norm_nonneg _
  calc
    _ ≤ a * ‖v.1‖ ^ 2 + b * ‖v.2‖ := hbound
    _ ≤ (1 + a + b) * ‖v.1‖ ^ 2 + (1 + a + b) * ‖v.2‖ := by gcongr <;> linarith
    _ = _ := by ring

/-- Elementary majorant calculation for the stable Taylor remainder. -/
theorem stable_remainder_majorant
    {T X W C : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hX : 0 ≤ X) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hsize : W ≤ C * (T ^ 2 + X)) :
    T * W + W ^ 2 + (T + W) * X ≤
      (1 + 2 * C + 2 * C ^ 2) * (T ^ 3 + T * X + X ^ 2) := by
  have hT2 : T ^ 2 ≤ T := by nlinarith
  have hT4 : T ^ 4 ≤ T ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hT1 (pow_nonneg hT 3)]
  have hTW : T * W ≤ C * (T ^ 3 + T * X) := by
    calc
      _ ≤ T * (C * (T ^ 2 + X)) := mul_le_mul_of_nonneg_left hsize hT
      _ = _ := by ring
  have hW2 : W ^ 2 ≤ 2 * C ^ 2 * (T ^ 3 + X ^ 2) := by
    have hs := mul_self_le_mul_self hW hsize
    have hsq := sq_nonneg (T ^ 2 - X)
    have hsq' := mul_nonneg (sq_nonneg C) hsq
    have hT4' := mul_le_mul_of_nonneg_left hT4 (show 0 ≤ 2 * C ^ 2 by positivity)
    nlinarith
  have hWX : (T + W) * X ≤ (1 + C) * (T * X + X ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right hsize hX
    have h₂ := mul_le_mul_of_nonneg_right hT2 hX
    have h₃ := mul_le_mul_of_nonneg_left h₂ hC
    nlinarith [sq_nonneg X]
  have hS0 : 0 ≤ T ^ 3 + T * X + X ^ 2 := by positivity
  calc
    _ ≤ C * (T ^ 3 + T * X) + 2 * C ^ 2 * (T ^ 3 + X ^ 2) +
        (1 + C) * (T * X + X ^ 2) := add_le_add (add_le_add hTW hW2) hWX
    _ ≤ C * (T ^ 3 + T * X + X ^ 2) +
        2 * C ^ 2 * (T ^ 3 + T * X + X ^ 2) +
        (1 + C) * (T ^ 3 + T * X + X ^ 2) := by
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg X]) hC
            · exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hT hX]) (by positivity)
          · exact mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg hT 3]) (by positivity)
    _ = _ := by ring

/-- The corresponding scalar Taylor remainder has one higher pure power. -/
theorem scalar_remainder_majorant
    {T X W E C : ℝ} (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hX : 0 ≤ X) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hsize : W ≤ C * (T ^ 2 + X)) (herr : E ≤ C * (T ^ 3 + X)) :
    T * E + W ^ 2 + (T + W) * X ≤
      (1 + 2 * C + 2 * C ^ 2) * (T ^ 4 + T * X + X ^ 2) := by
  have hT2 : T ^ 2 ≤ T := by nlinarith
  have hTE : T * E ≤ C * (T ^ 4 + T * X) := by
    calc
      _ ≤ T * (C * (T ^ 3 + X)) := mul_le_mul_of_nonneg_left herr hT
      _ = _ := by ring
  have hW2 : W ^ 2 ≤ 2 * C ^ 2 * (T ^ 4 + X ^ 2) := by
    have hs := mul_self_le_mul_self hW hsize
    have hsq' := mul_nonneg (sq_nonneg C) (sq_nonneg (T ^ 2 - X))
    nlinarith
  have hWX : (T + W) * X ≤ (1 + C) * (T * X + X ^ 2) := by
    have h₁ := mul_le_mul_of_nonneg_right hsize hX
    have h₂ := mul_le_mul_of_nonneg_right hT2 hX
    have h₃ := mul_le_mul_of_nonneg_left h₂ hC
    nlinarith [sq_nonneg X]
  calc
    _ ≤ C * (T ^ 4 + T * X) + 2 * C ^ 2 * (T ^ 4 + X ^ 2) +
        (1 + C) * (T * X + X ^ 2) := add_le_add (add_le_add hTE hW2) hWX
    _ ≤ C * (T ^ 4 + T * X + X ^ 2) +
        2 * C ^ 2 * (T ^ 4 + T * X + X ^ 2) +
        (1 + C) * (T ^ 4 + T * X + X ^ 2) := by
          apply add_le_add
          · apply add_le_add
            · exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg X]) hC
            · exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hT hX]) (by positivity)
          · exact mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg hT 4]) (by positivity)
    _ = _ := by ring

/-- The scalar function is defined from the constructed stable coordinate,
not supplied as an unrelated analytic function. -/
def reducedScalar
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (W : ℂ × (ι → ℂ) → (ι → ℂ))
    (v : ℂ × (ι → ℂ)) : ℂ :=
  ℓ (quadraticNonlinearity F p q (v.1 • r + W v) v.2)

theorem reducedScalar_analytic
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (W : ℂ × (ι → ℂ) → (ι → ℂ))
    (hW : AnalyticAt ℂ W 0) : AnalyticAt ℂ (reducedScalar F ℓ p q r W) 0 := by
  have hh : AnalyticAt ℂ (fun v : ℂ × (ι → ℂ) => v.1 • r + W v) 0 :=
    (analyticAt_fst.smul (analyticAt_const (v := r))).add hW
  exact (ℓ.analyticAt _).comp
    ((quadraticNonlinearity_analytic F p q _).comp (hh.prod analyticAt_snd))

/-- The two-variable scalar function whose roots control edge/cusp stability. -/
def spectralScalar
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (W : ℂ × (ι → ℂ) → (ι → ℂ)) (v : ℂ × ℂ) : ℂ :=
  reducedScalar F ℓ p q r W (v.1, v.2 • (1 : ι → ℂ))

theorem spectralScalar_analytic
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (W : ℂ × (ι → ℂ) → (ι → ℂ))
    (hW : AnalyticAt ℂ W 0) : AnalyticAt ℂ (spectralScalar F ℓ p q r W) 0 := by
  have hf : AnalyticAt ℂ (fun v : ℂ × ℂ => (v.1, v.2 • (1 : ι → ℂ))) 0 :=
    analyticAt_fst.prod (analyticAt_snd.smul (analyticAt_const (v := (1 : ι → ℂ))))
  have hred : AnalyticAt ℂ (reducedScalar F ℓ p q r W)
      ((fun v : ℂ × ℂ => (v.1, v.2 • (1 : ι → ℂ))) 0) := by
    simpa using reducedScalar_analytic F ℓ p q r W hW
  exact AnalyticAt.comp (f := fun v : ℂ × ℂ => (v.1, v.2 • (1 : ι → ℂ))) (x := 0) hred hf

/-- Norm estimate for every term of the exact scalar Taylor remainder. -/
theorem mixed_remainder_norm_bound
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w e ξ : ι → ℂ) (θ : ℂ)
    (D : ℝ) (hD : 0 ≤ D)
    (hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D)
    (hD₂ : ‖p‖ * ‖F‖ ≤ D)
    (hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D) :
    ‖θ • (p * r * F e + p * e * r) + p * w * F w + q * p * (θ • r + w) * ξ‖ ≤
      D * (‖θ‖ * ‖e‖ + ‖w‖ ^ 2 + (‖θ‖ + ‖w‖) * ‖ξ‖) := by
  have h₁ : ‖p * r * F e‖ ≤ ‖p‖ * ‖r‖ * (‖F‖ * ‖e‖) :=
    (triple_product_norm_bound _ _ _).trans
      (mul_le_mul_of_nonneg_left (F.le_opNorm _) (by positivity))
  have h₂ := triple_product_norm_bound p e r
  have h₃ : ‖p * w * F w‖ ≤ ‖p‖ * ‖w‖ * (‖F‖ * ‖w‖) :=
    (triple_product_norm_bound _ _ _).trans
      (mul_le_mul_of_nonneg_left (F.le_opNorm _) (by positivity))
  have hdisp : ‖θ • r + w‖ ≤ ‖θ‖ * ‖r‖ + ‖w‖ := by
    simpa only [norm_smul] using norm_add_le (θ • r) w
  have hdisp' : ‖θ‖ * ‖r‖ + ‖w‖ ≤ (‖r‖ + 1) * (‖θ‖ + ‖w‖) := by
    nlinarith [mul_nonneg (norm_nonneg r) (norm_nonneg w), norm_nonneg θ]
  have h₄ : ‖q * p * (θ • r + w) * ξ‖ ≤
      ‖q‖ * ‖p‖ * (‖r‖ + 1) * (‖θ‖ + ‖w‖) * ‖ξ‖ := by
    calc
      _ ≤ ‖q‖ * ‖p‖ * ‖θ • r + w‖ * ‖ξ‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (triple_product_norm_bound _ _ _) (norm_nonneg _))
      _ ≤ ‖q‖ * ‖p‖ * ((‖r‖ + 1) * (‖θ‖ + ‖w‖)) * ‖ξ‖ := by
        gcongr
        exact hdisp.trans hdisp'
      _ = _ := by ring
  calc
    _ ≤ ‖θ • (p * r * F e + p * e * r)‖ + ‖p * w * F w‖ +
        ‖q * p * (θ • r + w) * ξ‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ ‖θ‖ * (‖p‖ * ‖r‖ * (‖F‖ * ‖e‖) + ‖p‖ * ‖e‖ * ‖r‖) +
        ‖p‖ * ‖w‖ * (‖F‖ * ‖w‖) +
        ‖q‖ * ‖p‖ * (‖r‖ + 1) * (‖θ‖ + ‖w‖) * ‖ξ‖ := by
      rw [norm_smul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h₁ h₂))
          (norm_nonneg _)) h₃) h₄
    _ = (‖p‖ * ‖r‖ * (‖F‖ + 1)) * (‖θ‖ * ‖e‖) +
        (‖p‖ * ‖F‖) * ‖w‖ ^ 2 +
        (‖q‖ * ‖p‖ * (‖r‖ + 1)) * ((‖θ‖ + ‖w‖) * ‖ξ‖) := by ring
    _ ≤ D * (‖θ‖ * ‖e‖) + D * ‖w‖ ^ 2 + D * ((‖θ‖ + ‖w‖) * ‖ξ‖) := by gcongr
    _ = _ := by ring

/-- Full quantified scalar Taylor remainder, proved from the actual stable
coordinate errors and the computed quadratic/cubic coefficients. -/
theorem scalar_taylor_remainder_bound
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r A w ξ : ι → ℂ) (θ : ℂ) (hFr : F r = r)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D)
    (hD₂ : ‖p‖ * ‖F‖ ≤ D)
    (hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D)
    (hθ : ‖θ‖ ≤ 1)
    (hsize : ‖w‖ ≤ C * (‖θ‖ ^ 2 + ‖ξ‖))
    (herr : ‖w - θ ^ 2 • A‖ ≤ C * (‖θ‖ ^ 3 + ‖ξ‖)) :
    ‖ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) -
      θ ^ 2 * ℓ (p * r * r) - θ ^ 3 * ℓ (p * r * (F A + A)) - ℓ (q * ξ)‖ ≤
      (‖ℓ‖ * D * (1 + 2 * C + 2 * C ^ 2)) *
        (‖θ‖ ^ 4 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
  rw [scalar_reduction_coefficient_identity F ℓ p q r A w ξ θ hFr]
  apply (ℓ.le_opNorm _).trans
  have hnorm := mixed_remainder_norm_bound F p q r w (w - θ ^ 2 • A) ξ θ D hD hD₁ hD₂ hD₃
  have hmajor := scalar_remainder_majorant (norm_nonneg θ) hθ (norm_nonneg ξ)
    (norm_nonneg w) hC hsize herr
  calc
    _ ≤ ‖ℓ‖ * (D * (‖θ‖ * ‖w - θ ^ 2 • A‖ + ‖w‖ ^ 2 +
        (‖θ‖ + ‖w‖) * ‖ξ‖)) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ ‖ℓ‖ * (D * ((1 + 2 * C + 2 * C ^ 2) *
        (‖θ‖ ^ 4 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2))) := by gcongr
    _ = _ := by ring

/-- The second-order stable error follows from the actual fixed-point
equation and its quadratic size. Its constant is fully explicit. -/
theorem stable_second_order_error_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hFr : F r = r)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D)
    (hD₂ : ‖p‖ * ‖F‖ ≤ D)
    (hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D)
    (hθ : ‖θ‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1)
    (hsize : ‖w‖ ≤ C * (‖θ‖ ^ 2 + ‖ξ‖)) :
    ‖w - θ ^ 2 • K (p * r * r)‖ ≤
      (2 * ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) + ‖K‖ * ‖q‖) *
        (‖θ‖ ^ 3 + ‖ξ‖) := by
  have herr : ‖w - θ ^ 2 • K (p * r * r) - K (q * ξ)‖ ≤
      ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) *
        (‖θ‖ ^ 3 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
    rw [stable_fixed_point_remainder_identity F K p q r w ξ θ hFr hw]
    have hv := mixed_remainder_norm_bound F p q r w w ξ θ D hD hD₁ hD₂ hD₃
    have hm := stable_remainder_majorant (norm_nonneg θ) hθ (norm_nonneg ξ)
      (norm_nonneg w) hC hsize
    calc
      _ ≤ ‖K‖ * ‖θ • (p * r * F w + p * w * r) + p * w * F w +
          q * p * (θ • r + w) * ξ‖ := K.le_opNorm _
      _ ≤ ‖K‖ * (D * (‖θ‖ * ‖w‖ + ‖w‖ ^ 2 + (‖θ‖ + ‖w‖) * ‖ξ‖)) := by gcongr
      _ ≤ ‖K‖ * (D * ((1 + 2 * C + 2 * C ^ 2) *
          (‖θ‖ ^ 3 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2))) := by gcongr
      _ = _ := by ring
  have hminor : ‖θ‖ ^ 3 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2 ≤ 2 * (‖θ‖ ^ 3 + ‖ξ‖) := by
    nlinarith [norm_nonneg θ, norm_nonneg ξ, pow_nonneg (norm_nonneg θ) 3]
  have hforce : ‖K (q * ξ)‖ ≤ ‖K‖ * ‖q‖ * ‖ξ‖ := by
    calc
      _ ≤ ‖K‖ * ‖q * ξ‖ := K.le_opNorm _
      _ ≤ ‖K‖ * (‖q‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ‖(w - θ ^ 2 • K (p * r * r) - K (q * ξ)) + K (q * ξ)‖ := by
      congr 1
      abel
    _ ≤ ‖w - θ ^ 2 • K (p * r * r) - K (q * ξ)‖ + ‖K (q * ξ)‖ := norm_add_le _ _
    _ ≤ ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) *
        (2 * (‖θ‖ ^ 3 + ‖ξ‖)) + ‖K‖ * ‖q‖ * ‖ξ‖ :=
      add_le_add (herr.trans (mul_le_mul_of_nonneg_left hminor (by positivity))) hforce
    _ ≤ ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) *
        (2 * (‖θ‖ ^ 3 + ‖ξ‖)) + ‖K‖ * ‖q‖ * (‖θ‖ ^ 3 + ‖ξ‖) := by
          gcongr
          nlinarith [pow_nonneg (norm_nonneg θ) 3]
    _ = _ := by ring

/-- Uniform Taylor estimate for the scalar reduction associated with any
actual local stable map having the proved quadratic size estimate. -/
theorem stable_map_scalar_taylor_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (hfixed : ∀ v, ‖v‖ < ε → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (hsize : ∀ v, ‖v‖ < ε → ‖W v‖ ≤ C * (‖v.1‖ ^ 2 + ‖v.2‖)) :
    ∃ δ > 0, ∃ B > 0, ∀ v : ℂ × (ι → ℂ), ‖v‖ < δ →
      ‖reducedScalar F ℓ p q r W v - v.1 ^ 2 * ℓ (p * r * r) -
        v.1 ^ 3 * ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) - ℓ (q * v.2)‖ ≤
        B * (‖v.1‖ ^ 4 + ‖v.1‖ * ‖v.2‖ + ‖v.2‖ ^ 2) := by
  let D := 1 + ‖p‖ * ‖r‖ * (‖F‖ + 1) + ‖p‖ * ‖F‖ + ‖q‖ * ‖p‖ * (‖r‖ + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd₁ : 0 ≤ ‖p‖ * ‖r‖ * (‖F‖ + 1) := by positivity
  have hd₂ : 0 ≤ ‖p‖ * ‖F‖ := by positivity
  have hd₃ : 0 ≤ ‖q‖ * ‖p‖ * (‖r‖ + 1) := by positivity
  have hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D := by dsimp [D]; linarith
  have hD₂ : ‖p‖ * ‖F‖ ≤ D := by dsimp [D]; linarith
  have hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D := by dsimp [D]; linarith
  let E := 2 * ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) + ‖K‖ * ‖q‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let C' := C + E
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  let B := ‖ℓ‖ * D * (1 + 2 * C' + 2 * C' ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨min ε 1, lt_min hε zero_lt_one, 1 + B, by positivity, ?_⟩
  intro v hv
  have hvε : ‖v‖ < ε := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ ≤ 1 := (lt_of_lt_of_le hv (min_le_right _ _)).le
  have hθ : ‖v.1‖ ≤ 1 := (norm_fst_le v).trans hv1
  have hξ : ‖v.2‖ ≤ 1 := (norm_snd_le v).trans hv1
  have hs : ‖W v‖ ≤ C' * (‖v.1‖ ^ 2 + ‖v.2‖) :=
    (hsize v hvε).trans (mul_le_mul_of_nonneg_right
      (show C ≤ C' by dsimp [C']; linarith) (by positivity))
  have he : ‖W v - v.1 ^ 2 • K (p * r * r)‖ ≤ C' * (‖v.1‖ ^ 3 + ‖v.2‖) := by
    have hh := stable_second_order_error_bound F K p q r (W v) v.2 v.1 hFr
      (hfixed v hvε) C D hC.le hD hD₁ hD₂ hD₃ hθ hξ (hsize v hvε)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (show E ≤ C' by dsimp [C']; linarith) (by positivity))
  have ht := scalar_taylor_remainder_bound F ℓ p q r (K (p * r * r)) (W v) v.2 v.1
    hFr C' D hC' hD hD₁ hD₂ hD₃ hθ hs he
  exact ht.trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith : B ≤ 1 + B) (by positivity))

/-- A single uniform scalar Taylor constant works for all sufficiently small
actual stable fixed points, independently of how they were parametrized. -/
theorem fixed_point_uniform_scalar_taylor_of_size
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B > 0, ∀ (θ : ℂ) (w ξ : ι → ℂ),
      w = K (quadraticNonlinearity F p q (θ • r + w) ξ) →
      ‖θ‖ ≤ 1 → ‖ξ‖ ≤ 1 → ‖w‖ ≤ C * (‖θ‖ ^ 2 + ‖ξ‖) →
      ‖ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) - θ ^ 2 * ℓ (p * r * r) -
        θ ^ 3 * ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) - ℓ (q * ξ)‖ ≤
        B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
  let D := 1 + ‖p‖ * ‖r‖ * (‖F‖ + 1) + ‖p‖ * ‖F‖ + ‖q‖ * ‖p‖ * (‖r‖ + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hd₁ : 0 ≤ ‖p‖ * ‖r‖ * (‖F‖ + 1) := by positivity
  have hd₂ : 0 ≤ ‖p‖ * ‖F‖ := by positivity
  have hd₃ : 0 ≤ ‖q‖ * ‖p‖ * (‖r‖ + 1) := by positivity
  have hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D := by dsimp [D]; linarith
  have hD₂ : ‖p‖ * ‖F‖ ≤ D := by dsimp [D]; linarith
  have hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D := by dsimp [D]; linarith
  let E := 2 * ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) + ‖K‖ * ‖q‖
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let C' := C + E
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  let B := ‖ℓ‖ * D * (1 + 2 * C' + 2 * C' ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1 + B, by positivity, ?_⟩
  intro θ w ξ hw hθ hξ hs
  have hs' : ‖w‖ ≤ C' * (‖θ‖ ^ 2 + ‖ξ‖) := hs.trans
    (mul_le_mul_of_nonneg_right (show C ≤ C' by dsimp [C']; linarith) (by positivity))
  have he : ‖w - θ ^ 2 • K (p * r * r)‖ ≤ C' * (‖θ‖ ^ 3 + ‖ξ‖) := by
    have hh := stable_second_order_error_bound F K p q r w ξ θ hFr hw C D hC hD hD₁ hD₂ hD₃ hθ hξ hs
    exact hh.trans (mul_le_mul_of_nonneg_right (show E ≤ C' by dsimp [C']; linarith) (by positivity))
  exact (scalar_taylor_remainder_bound F ℓ p q r (K (p * r * r)) w ξ θ hFr
    C' D hC' hD hD₁ hD₂ hD₃ hθ hs' he).trans
    (mul_le_mul_of_nonneg_right (show B ≤ 1 + B by linarith) (by positivity))

/-- Uniform Taylor bound for all small fixed points, without choosing a
particular analytic parametrization. -/
theorem fixed_point_uniform_scalar_taylor
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r) :
    ∃ B > 0, ∀ (θ : ℂ) (w ξ : ι → ℂ),
      w = K (quadraticNonlinearity F p q (θ • r + w) ξ) →
      ‖θ • r + w‖ ≤ 1 → 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖w‖ ≤ 1 →
      ‖θ‖ ≤ 1 → ‖ξ‖ ≤ 1 →
      ‖ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) - θ ^ 2 * ℓ (p * r * r) -
        θ ^ 3 * ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) - ℓ (q * ξ)‖ ≤
        B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
  let a := 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2
  let b := 2 * ‖K‖ * ‖q‖ * (1 + ‖p‖)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  obtain ⟨B, hB, hTaylor⟩ := fixed_point_uniform_scalar_taylor_of_size F K ℓ p q r hFr
    (1 + a + b) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro θ w ξ hw hlocal hsmall hθ hξ
  apply hTaylor θ w ξ hw hθ hξ
  have hh : ‖w‖ ≤ a * ‖θ‖ ^ 2 + b * ‖ξ‖ :=
    stable_fixed_point_size F K p q r w ξ θ hw hlocal hsmall
  calc
    _ ≤ a * ‖θ‖ ^ 2 + b * ‖ξ‖ := hh
    _ ≤ (1 + a + b) * ‖θ‖ ^ 2 + (1 + a + b) * ‖ξ‖ := by gcongr <;> linarith
    _ = _ := by ring

/-- The local Lipschitz estimate used for both scalar forcing and vector
reconstruction follows from Mathlib's analytic-to-C¹ and mean-value results. -/
theorem analytic_local_lipschitz
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (f : E → G) (hf : AnalyticAt ℂ f 0) :
    ∃ ε > 0, ∃ C > 0, ∀ x y, ‖x‖ < ε → ‖y‖ < ε →
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨K, s, hs, hLip⟩ := (hf.contDiffAt (n := 1)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε, hε, (K : ℝ) + 1, by positivity, ?_⟩
  intro x y hx hy
  have hx' : x ∈ s := hsub (by simpa using hx)
  have hy' : y ∈ s := hsub (by simpa using hy)
  have h := hLip.dist_le_mul x hx' y hy'
  simp only [dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- The scalar residual changes by at most a fixed multiple of the actual
forcing error, even though the stable coordinate changes with that forcing. -/
theorem scalar_forcing_residual_bound
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (W : ℂ × (ι → ℂ) → (ι → ℂ))
    (hW : AnalyticAt ℂ W 0) :
    ∃ ε > 0, ∃ C > 0, ∀ θ ω R,
      ‖(θ, ω • (1 : ι → ℂ))‖ < ε →
      ‖(θ, ω • (1 : ι → ℂ) + R)‖ < ε →
      reducedScalar F ℓ p q r W (θ, ω • (1 : ι → ℂ) + R) = 0 →
      ‖spectralScalar F ℓ p q r W (θ, ω)‖ ≤ C * ‖R‖ := by
  obtain ⟨ε, hε, C, hC, hLip⟩ := analytic_local_lipschitz
    (reducedScalar F ℓ p q r W) (reducedScalar_analytic F ℓ p q r W hW)
  refine ⟨ε, hε, C, hC, ?_⟩
  intro θ ω R hx hy hzero
  have h := hLip (θ, ω • (1 : ι → ℂ)) (θ, ω • (1 : ι → ℂ) + R) hx hy
  simpa [spectralScalar, hzero, Prod.norm_def] using h

end NonSymmetricDyson.Full.Nonlinear
