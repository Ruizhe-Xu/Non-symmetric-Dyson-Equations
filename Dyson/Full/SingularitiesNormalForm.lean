import Dyson.Full.Singularities
import Dyson.Full.SingularitiesJets
import Dyson.Full.NonlinearAnalytic

/-! Assembly of the actual normalized solution curve, the proved stable
Taylor estimate, and the scalar monomial normal-form theorem. -/

noncomputable section
open Filter
open scoped Topology

namespace NonSymmetricDyson.Full.Singularities

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem quadraticNonlinearity_eq_normalized
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q h ξ : ι → ℂ) :
    Nonlinear.quadraticNonlinearity F p q h ξ =
      normalizedNonlinearity F.toLinearMap p q h ξ := rfl

/-- The actual analytic energy graph has the manuscript's computed scalar
Taylor estimate. This theorem uses the proved finite-vector fixed-point error
estimate, rather than assuming a Dyson-specific Taylor expansion. -/
theorem exists_energy_curve_with_scalar_taylor_and_uniqueness
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0) (hFr : F r = r)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      (∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
          curve (ℓ v.2) = v) ∧
      ∃ B > 0, ∀ᶠ θ in 𝓝 (0 : ℂ),
        ‖ℓ q * (curve θ).1 + ℓ (p * r * r) * θ ^ 2 +
          ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) * θ ^ 3‖ ≤
          B * (‖θ‖ ^ 4 + ‖(curve θ).1‖ * ‖θ‖ + ‖(curve θ).1‖ ^ 2) := by
  obtain ⟨curve, hca, hc0, hc, huniq⟩ :=
    exists_normalized_analytic_parametrization F ℓ p q r hμ hlF hsimple
  obtain ⟨B, hB, hTaylor⟩ := Nonlinear.fixed_point_uniform_scalar_taylor F K ℓ p q r hFr
  let stable : ℂ → ι → ℂ := fun θ => (curve θ).2 - θ • r
  have hstable0 : stable 0 = 0 := by simp [stable, hc0]
  have hstablecont : ContinuousAt stable 0 :=
    hca.continuousAt.snd.sub (continuousAt_id.smul continuousAt_const)
  have hsmall : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(curve θ).2‖ ≤ 1 ∧ 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖stable θ‖ ≤ 1 ∧
        ‖θ‖ ≤ 1 ∧ ‖(curve θ).1‖ ≤ 1 := by
    have h₁ := hca.continuousAt.snd.norm.eventually_lt continuousAt_const
      (show ‖(curve 0).2‖ < 1 by simp [hc0])
    have h₂ := (continuousAt_const.mul hstablecont.norm).eventually_lt continuousAt_const
      (show 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖stable 0‖ < 1 by simp [hstable0])
    have h₃ := continuousAt_id.norm.eventually_lt continuousAt_const
      (show ‖(0 : ℂ)‖ < (1 : ℝ) by norm_num)
    have h₄ := hca.continuousAt.fst.norm.eventually_lt continuousAt_const
      (show ‖(curve 0).1‖ < 1 by simp [hc0])
    filter_upwards [h₁, h₂, h₃, h₄] with θ h₁ h₂ h₃ h₄
    exact ⟨h₁.le, h₂.le, h₃.le, h₄.le⟩
  refine ⟨curve, hca, hc0, hc, huniq, B, hB, ?_⟩
  filter_upwards [hc, hsmall] with θ hθ hsm
  have hrec : θ • r + stable θ = (curve θ).2 := by dsimp [stable]; abel
  have hproj := (projected_residual_iff F.toLinearMap K.toLinearMap ℓ.toLinearMap r
    (curve θ).2 (normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1))
    hlF hK.kill_right hFr hK.left_inverse hK.right_inverse).mp hθ.2
  have hfixed : stable θ = K (Nonlinear.quadraticNonlinearity F p q
      (θ • r + stable θ) (fun _ => (curve θ).1)) := by
    rw [hrec, quadraticNonlinearity_eq_normalized]
    dsimp [stable]
    have hp := hproj.1
    change (curve θ).2 = ℓ (curve θ).2 • r + K (normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) at hp
    rw [hθ.1] at hp
    linear_combination hp
  have ht := hTaylor θ (stable θ) (fun _ => (curve θ).1) hfixed
    (by simpa only [hrec] using hsm.1) hsm.2.1 hsm.2.2.1
    (by simpa only [pi_norm_const] using hsm.2.2.2)
  have hzero : ℓ (Nonlinear.quadraticNonlinearity F p q
      (θ • r + stable θ) (fun _ => (curve θ).1)) = 0 := by
    rw [hrec, quadraticNonlinearity_eq_normalized]
    exact hproj.2
  have hforce : ℓ (q * (fun _ => (curve θ).1)) = (curve θ).1 * ℓ q := by
    have he : q * (fun _ => (curve θ).1) = (curve θ).1 • q := by
      ext i
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, map_smul, smul_eq_mul]
  rw [hzero, hforce, pi_norm_const] at ht
  have he : -(ℓ q * (curve θ).1 + ℓ (p * r * r) * θ ^ 2 +
      ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) * θ ^ 3) =
      0 - θ ^ 2 * ℓ (p * r * r) -
        θ ^ 3 * ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) -
        (curve θ).1 * ℓ q := by ring
  rw [← he, norm_neg] at ht
  simpa only [mul_comm ‖θ‖ ‖(curve θ).1‖] using ht

theorem exists_energy_curve_with_scalar_taylor
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0) (hFr : F r = r)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      ∃ B > 0, ∀ᶠ θ in 𝓝 (0 : ℂ),
        ‖ℓ q * (curve θ).1 + ℓ (p * r * r) * θ ^ 2 +
          ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) * θ ^ 3‖ ≤
          B * (‖θ‖ ^ 4 + ‖(curve θ).1‖ * ‖θ‖ + ‖(curve θ).1‖ ^ 2) := by
  obtain ⟨curve, hca, hc0, hc, _, hTaylor⟩ :=
    exists_energy_curve_with_scalar_taylor_and_uniqueness F K ℓ p q r hμ hFr hlF hsimple hK
  exact ⟨curve, hca, hc0, hc, hTaylor⟩

/-- Exact quadratic-or-cubic normal forms for the actual normalized Dyson
system. The analytic coefficients and remainder come from the preceding
proved theorem. The sole external input here is the general one-variable
monomial-normal-form principle. -/
theorem normalized_system_exact_normal_forms
    (externalNormalForm : AnalyticMonomialNormalFormPrinciple)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (μ : ℝ) (hμpos : 0 < μ) (hμeq : ℓ q = (μ : ℂ))
    (hFr : F r = r) (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r)
    (hnd : ℓ (p * r * r) ≠ 0 ∨
      ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) ≠ 0) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      ((ℓ (p * r * r) ≠ 0 ∧ ∃ χ : ℂ → ℂ,
        AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
        ∀ᶠ s in 𝓝 (0 : ℂ), (curve (χ s)).1 = -(ℓ (p * r * r) / (μ : ℂ)) * s ^ 2) ∨
      (ℓ (p * r * r) = 0 ∧ ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) ≠ 0 ∧
        ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
        ∀ᶠ s in 𝓝 (0 : ℂ), (curve (χ s)).1 =
          -(ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) / (μ : ℂ)) * s ^ 3)) := by
  have hμ : ℓ q ≠ 0 := by rw [hμeq]; exact_mod_cast hμpos.ne'
  obtain ⟨curve, hca, hc0, hcur, B, hB, hTaylor⟩ :=
    exists_energy_curve_with_scalar_taylor F K ℓ p q r hμ hFr hlF hsimple hK
  refine ⟨curve, hca, hc0, hcur, ?_⟩
  apply quadratic_or_cubic_energy_normal_form externalNormalForm μ B
    (ℓ (p * r * r)) (ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))))
    (fun θ => (curve θ).1) hμpos hB.le hnd
  · exact ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt _).comp hca
  · simp [hc0]
  · simpa only [hμeq] using hTaylor

end NonSymmetricDyson.Full.Singularities
