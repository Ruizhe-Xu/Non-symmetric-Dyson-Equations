import Dyson.Full.SingularitiesNormalForm
import Dyson.Full.SingularitiesReflection
import Dyson.Full.SingularitiesDensity

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- The real-preserving version of the universal one-variable monomial
normal-form theorem. The normalization of the derivative fixes the local
root of the analytic unit. This input contains no Dyson assertion. -/
def RealAnalyticMonomialNormalFormPrinciple : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℂ) (k : ℕ), AnalyticAt ℂ f 0 → f 0 = 0 →
    c ≠ 0 → 1 ≤ k → RealAnalyticGerm f → star c = c →
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => f z - c * z ^ k)
      (fun z => z ^ (k + 1)) →
    ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      RealAnalyticGerm χ ∧ ∀ᶠ s in 𝓝 (0 : ℂ), f (χ s) = c * s ^ k

theorem implicit_energy_real_exact_normal_form
    (externalNormalForm : RealAnalyticMonomialNormalFormPrinciple)
    (μ C : ℝ) (γ : ℂ) (k : ℕ) (Ω R : ℂ → ℂ)
    (hμ : 0 < μ) (hC : 0 ≤ C) (hγ : γ ≠ 0) (hk : 1 ≤ k)
    (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0)
    (hΩreal : RealAnalyticGerm Ω) (hγreal : star γ = γ)
    (heq : ∀ᶠ θ in 𝓝 (0 : ℂ), (μ : ℂ) * Ω θ + γ * θ ^ k + R θ = 0)
    (hR : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖R θ‖ ≤ C * (‖θ‖ ^ (k + 1) + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      RealAnalyticGerm χ ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(γ / (μ : ℂ)) * s ^ k := by
  apply externalNormalForm Ω (-(γ / (μ : ℂ))) k hΩ hΩ0
  · exact neg_ne_zero.mpr (div_ne_zero hγ (by exact_mod_cast hμ.ne'))
  · exact hk
  · exact hΩreal
  · simp [hγreal]
  · simpa only [neg_mul, sub_neg_eq_add] using
      implicit_energy_graph_jet μ C γ k Ω R hμ hC hk hΩ hΩ0 heq hR

theorem quadratic_or_cubic_real_energy_normal_form
    (externalNormalForm : RealAnalyticMonomialNormalFormPrinciple)
    (μ C : ℝ) (σ ψ : ℂ) (Ω : ℂ → ℂ) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hnd : σ ≠ 0 ∨ ψ ≠ 0) (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0)
    (hΩreal : RealAnalyticGerm Ω) (hσreal : star σ = σ) (hψreal : star ψ = ψ)
    (hR : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(μ : ℂ) * Ω θ + σ * θ ^ 2 + ψ * θ ^ 3‖ ≤
        C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    (σ ≠ 0 ∧ ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧ RealAnalyticGerm χ ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(σ / (μ : ℂ)) * s ^ 2) ∨
    (σ = 0 ∧ ψ ≠ 0 ∧ ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧ RealAnalyticGerm χ ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(ψ / (μ : ℂ)) * s ^ 3) := by
  by_cases hσ : σ = 0
  · right
    have hψ : ψ ≠ 0 := hnd.resolve_left (not_not_intro hσ)
    refine ⟨hσ, hψ, ?_⟩
    apply implicit_energy_real_exact_normal_form externalNormalForm μ C ψ 3 Ω
      (fun θ => -((μ : ℂ) * Ω θ + ψ * θ ^ 3)) hμ hC hψ (by norm_num) hΩ hΩ0 hΩreal hψreal
    · exact Filter.Eventually.of_forall fun θ => by ring
    · filter_upwards [hR] with θ ht
      simpa only [hσ, zero_mul, add_zero, norm_neg] using ht
  · left
    refine ⟨hσ, ?_⟩
    have hC' : 0 ≤ C + ‖ψ‖ := add_nonneg hC (norm_nonneg _)
    apply implicit_energy_real_exact_normal_form externalNormalForm μ (C + ‖ψ‖) σ 2 Ω
      (fun θ => -((μ : ℂ) * Ω θ + σ * θ ^ 2)) hμ hC' hσ (by norm_num) hΩ hΩ0 hΩreal hσreal
    · exact Filter.Eventually.of_forall fun θ => by ring
    · have hθsmall : ∀ᶠ θ : ℂ in 𝓝 0, ‖θ‖ ≤ 1 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with θ hθ
        exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hθ)
      filter_upwards [hR, hθsmall] with θ ht hθ
      have hpow : ‖θ‖ ^ 4 ≤ ‖θ‖ ^ 3 :=
        pow_le_pow_of_le_one (norm_nonneg _) hθ (by norm_num)
      have hn : ‖(μ : ℂ) * Ω θ + σ * θ ^ 2‖ ≤
          ‖(μ : ℂ) * Ω θ + σ * θ ^ 2 + ψ * θ ^ 3‖ + ‖ψ‖ * ‖θ‖ ^ 3 := by
        have hh := norm_sub_le ((μ : ℂ) * Ω θ + σ * θ ^ 2 + ψ * θ ^ 3) (ψ * θ ^ 3)
        simpa only [add_sub_cancel_right, norm_mul, norm_pow] using hh
      rw [norm_neg]
      calc
        _ ≤ C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) + ‖ψ‖ * ‖θ‖ ^ 3 :=
          hn.trans (add_le_add_right ht _)
        _ ≤ C * (‖θ‖ ^ 3 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) + ‖ψ‖ * ‖θ‖ ^ 3 := by gcongr
        _ ≤ (C + ‖ψ‖) * (‖θ‖ ^ (2 + 1) + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) := by
          have hnon := mul_nonneg (norm_nonneg ψ)
            (show 0 ≤ ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2 by positivity)
          norm_num only [Nat.reduceAdd]
          nlinarith

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Reflection of any locally unique normalized solution parametrization. -/
theorem normalized_curve_reflection
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q : ι → ℂ) (hFreal : ∀ x, F (star x) = star (F x))
    (hℓreal : ∀ x, ℓ (star x) = star (ℓ x)) (hp : star p = p) (hq : star q = q)
    (curve : ℂ → ℂ × (ι → ℂ)) (hca : AnalyticAt ℂ curve 0) (hc0 : curve 0 = 0)
    (hc : ∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
      (curve θ).2 - F (curve θ).2 =
        normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1))
    (huniq : ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
      v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
        curve (ℓ v.2) = v) :
    ∀ᶠ θ in 𝓝 (0 : ℂ), curve (star θ) = star (curve θ) := by
  have hstar : Tendsto (fun θ => star (curve θ)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [hc0, star_zero] using hca.continuousAt.star.tendsto
  filter_upwards [hc, hstar.eventually huniq] with θ hθ hu
  have hres : (star (curve θ)).2 - F (star (curve θ)).2 =
      normalizedNonlinearity F.toLinearMap p q (star (curve θ)).2
        (fun _ => (star (curve θ)).1) := by
    have hh := congrArg star hθ.2
    simpa only [star_sub, ← hFreal, ← normalizedNonlinearity_conjugate F p q _ _ hFreal hp hq]
      using hh
  have hh := hu hres
  change curve (ℓ (star (curve θ).2)) = star (curve θ) at hh
  rwa [hℓreal, hθ.1] at hh

/-- The full normalized Dyson system has a real analytic quadratic or cubic
chart, with its actual vector tangent and local uniqueness retained. -/
theorem normalized_system_real_chart
    (externalNormalForm : RealAnalyticMonomialNormalFormPrinciple)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (μ : ℝ) (hμpos : 0 < μ) (hμeq : ℓ q = (μ : ℂ))
    (hFr : F r = r) (hnorm : ℓ r = 1) (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r)
    (hFreal : ∀ x, F (star x) = star (F x))
    (hℓreal : ∀ x, ℓ (star x) = star (ℓ x)) (hp : star p = p) (hq : star q = q)
    (σ ψ : ℝ) (hσ : ℓ (p * r * r) = (σ : ℂ))
    (hψ : ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) = (ψ : ℂ))
    (hnd : σ ≠ 0 ∨ 0 < ψ) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), ∃ k : ℕ, ∃ c : ℝ, ∃ χ : ℂ → ℂ,
      AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧ HasDerivAt curve (0, r) 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      (∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
          curve (ℓ v.2) = v) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), curve (star θ) = star (curve θ)) ∧
      AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧ RealAnalyticGerm χ ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), (curve (χ s)).1 = (c : ℂ) * s ^ k) ∧
      ((k = 2 ∧ σ ≠ 0 ∧ c = -(σ / μ)) ∨
        (k = 3 ∧ σ = 0 ∧ 0 < ψ ∧ c = -(ψ / μ))) := by
  have hμ : ℓ q ≠ 0 := by rw [hμeq]; exact_mod_cast hμpos.ne'
  obtain ⟨curve, hca, hc0, hc, hu, B, hB, ht⟩ :=
    exists_energy_curve_with_scalar_taylor_and_uniqueness F K ℓ p q r hμ hFr hlF hsimple hK
  have href := normalized_curve_reflection F ℓ p q hFreal hℓreal hp hq curve hca hc0 hc hu
  have hΩa : AnalyticAt ℂ (fun θ => (curve θ).1) 0 :=
    ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt _).comp hca
  have hΩreal : RealAnalyticGerm (fun θ => (curve θ).1) := by
    filter_upwards [href] with θ hθ
    exact congrArg Prod.fst hθ
  have hcoeff : (σ : ℂ) ≠ 0 ∨ (ψ : ℂ) ≠ 0 := by
    rcases hnd with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h.ne')
  have hforms := quadratic_or_cubic_real_energy_normal_form externalNormalForm μ B
    (σ : ℂ) (ψ : ℂ) (fun θ => (curve θ).1) hμpos hB.le hcoeff hΩa
    (by simp [hc0]) hΩreal (by simp) (by simp) (by simpa only [hμeq, hσ, hψ] using ht)
  have hd := normalized_solution_curve_tangent F ℓ p q r hμ hFr hnorm hlF hsimple curve hca hc0 hc
  rcases hforms with ⟨hs, χ, hχa, hχ0, hχd, hχreal, hform⟩ |
    ⟨hs, hp', χ, hχa, hχ0, hχd, hχreal, hform⟩
  · refine ⟨curve, 2, -(σ / μ), χ, hca, hc0, hd, hc, hu, href,
      hχa, hχ0, hχd, hχreal, ?_, Or.inl ⟨rfl, ?_, rfl⟩⟩
    · simpa only [Complex.ofReal_neg, Complex.ofReal_div] using hform
    · exact_mod_cast hs
  · have hs' : σ = 0 := by exact_mod_cast hs
    refine ⟨curve, 3, -(ψ / μ), χ, hca, hc0, hd, hc, hu, href,
      hχa, hχ0, hχd, hχreal, ?_, Or.inr ⟨rfl, hs', ?_, rfl⟩⟩
    · simpa only [Complex.ofReal_neg, Complex.ofReal_div] using hform
    · exact hnd.resolve_left (not_not_intro hs')

end NonSymmetricDyson.Full.Singularities
