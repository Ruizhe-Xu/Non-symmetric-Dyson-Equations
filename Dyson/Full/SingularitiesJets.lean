import Mathlib

/-! Pointwise analytic-jet estimates for the implicit scalar energy graph.
These are proved from the actual residual equation and explicit error bound. -/

noncomputable section
open Filter
open scoped Topology

namespace NonSymmetricDyson.Full.Singularities

/-- Absorbing the terms containing the implicit energy gives its correct
quadratic/cubic order. The statement is uniform in the monomial degree. -/
theorem implicit_monomial_size_bound (μ C : ℝ) (γ θ w R : ℂ) (k : ℕ)
    (hμ : 0 < μ) (hC : 0 ≤ C) (hθ : ‖θ‖ ≤ 1)
    (heq : (μ : ℂ) * w + γ * θ ^ k + R = 0)
    (hR : ‖R‖ ≤ C * (‖θ‖ ^ (k + 1) + ‖w‖ * ‖θ‖ + ‖w‖ ^ 2))
    (hsmall : C * (‖θ‖ + ‖w‖) ≤ μ / 2) :
    ‖w‖ ≤ (2 * (‖γ‖ + C) / μ) * ‖θ‖ ^ k := by
  have hpow : ‖θ‖ ^ (k + 1) ≤ ‖θ‖ ^ k :=
    pow_le_pow_of_le_one (norm_nonneg _) hθ (Nat.le_succ k)
  have hnormμ : ‖(μ : ℂ)‖ = μ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ]
  have he : (μ : ℂ) * w = -(γ * θ ^ k + R) := by linear_combination heq
  have hleft : μ * ‖w‖ ≤ ‖γ‖ * ‖θ‖ ^ k + ‖R‖ := by
    calc
      _ = ‖(μ : ℂ) * w‖ := by rw [norm_mul, hnormμ]
      _ = ‖γ * θ ^ k + R‖ := by rw [he, norm_neg]
      _ ≤ ‖γ * θ ^ k‖ + ‖R‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_pow]
  have hrmajor : ‖R‖ ≤ C * ‖θ‖ ^ k + μ / 2 * ‖w‖ := by
    calc
      _ ≤ C * (‖θ‖ ^ (k + 1) + ‖w‖ * ‖θ‖ + ‖w‖ ^ 2) := hR
      _ = C * ‖θ‖ ^ (k + 1) + (C * (‖θ‖ + ‖w‖)) * ‖w‖ := by ring
      _ ≤ C * ‖θ‖ ^ k + μ / 2 * ‖w‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hC)
          (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hμ).mpr
  linarith

/-- Once the implicit energy has order `k`, the residual estimate yields the
full leading Taylor term with an explicit remainder of order `k+1`. -/
theorem implicit_monomial_jet_bound (μ C B : ℝ) (γ θ w R : ℂ) (k : ℕ)
    (hμ : 0 < μ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hk : 1 ≤ k)
    (hθ : ‖θ‖ ≤ 1)
    (heq : (μ : ℂ) * w + γ * θ ^ k + R = 0)
    (hR : ‖R‖ ≤ C * (‖θ‖ ^ (k + 1) + ‖w‖ * ‖θ‖ + ‖w‖ ^ 2))
    (hw : ‖w‖ ≤ B * ‖θ‖ ^ k) :
    ‖w + (γ / (μ : ℂ)) * θ ^ k‖ ≤
      (C * (1 + B + B ^ 2) / μ) * ‖θ‖ ^ (k + 1) := by
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hnormμ : ‖(μ : ℂ)‖ = μ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ]
  have hmix : ‖w‖ * ‖θ‖ ≤ B * ‖θ‖ ^ (k + 1) := by
    calc
      _ ≤ (B * ‖θ‖ ^ k) * ‖θ‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := by rw [pow_succ]; ring
  have hpow : ‖θ‖ ^ (k + k) ≤ ‖θ‖ ^ (k + 1) :=
    pow_le_pow_of_le_one (norm_nonneg _) hθ (by omega)
  have hsq : ‖w‖ ^ 2 ≤ B ^ 2 * ‖θ‖ ^ (k + 1) := by
    calc
      _ ≤ (B * ‖θ‖ ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = B ^ 2 * ‖θ‖ ^ (k + k) := by simp only [pow_two, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hrmajor : ‖R‖ ≤ C * (1 + B + B ^ 2) * ‖θ‖ ^ (k + 1) := by
    calc
      _ ≤ C * (‖θ‖ ^ (k + 1) + ‖w‖ * ‖θ‖ + ‖w‖ ^ 2) := hR
      _ ≤ C * (‖θ‖ ^ (k + 1) + B * ‖θ‖ ^ (k + 1) +
          B ^ 2 * ‖θ‖ ^ (k + 1)) := by gcongr
      _ = _ := by ring
  have he : w + (γ / (μ : ℂ)) * θ ^ k = -R / (μ : ℂ) := by
    apply (eq_div_iff hμ0).mpr
    field_simp [hμ0]
    linear_combination heq
  rw [he, norm_div, norm_neg, hnormμ, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hrmajor hμ.le

/-- The preceding pointwise estimates give the Taylor jet of an actual
implicit analytic energy graph. The smallness assumptions are deduced from
continuity at zero rather than included among the hypotheses. -/
theorem implicit_energy_graph_jet (μ C : ℝ) (γ : ℂ) (k : ℕ)
    (Ω R : ℂ → ℂ) (hμ : 0 < μ) (hC : 0 ≤ C) (hk : 1 ≤ k)
    (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0)
    (heq : ∀ᶠ θ in 𝓝 (0 : ℂ), (μ : ℂ) * Ω θ + γ * θ ^ k + R θ = 0)
    (hR : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖R θ‖ ≤ C * (‖θ‖ ^ (k + 1) + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun θ => Ω θ + (γ / (μ : ℂ)) * θ ^ k) (fun θ => θ ^ (k + 1)) := by
  let B : ℝ := 2 * (‖γ‖ + C) / μ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hθsmall : ∀ᶠ θ : ℂ in 𝓝 0, ‖θ‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with θ hθ
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hθ)
  have hsmallcont : ContinuousAt (fun θ : ℂ => C * (‖θ‖ + ‖Ω θ‖)) 0 :=
    continuousAt_const.mul (continuousAt_id.norm.add hΩ.continuousAt.norm)
  have hsmall : ∀ᶠ θ : ℂ in 𝓝 0, C * (‖θ‖ + ‖Ω θ‖) ≤ μ / 2 := by
    have hh := hsmallcont.tendsto.eventually_lt_const
      (show C * (‖(0 : ℂ)‖ + ‖Ω 0‖) < μ / 2 by rw [hΩ0]; simpa using half_pos hμ)
    exact hh.mono fun θ hθ => hθ.le
  apply Asymptotics.IsBigO.of_bound (C * (1 + B + B ^ 2) / μ)
  filter_upwards [heq, hR, hθsmall, hsmall] with θ he hr ht hs
  rw [norm_pow]
  exact implicit_monomial_jet_bound μ C B γ θ (Ω θ) (R θ) k hμ hC hB hk ht he hr
    (implicit_monomial_size_bound μ C γ θ (Ω θ) (R θ) k hμ hC ht he hr hs)

/-- A precise external statement of the classical one-variable analytic
normal-form theorem at a zero of finite order. This is independent of Dyson
matrices and does not assert coefficient nondegeneracy or a physical branch. -/
def AnalyticMonomialNormalFormPrinciple : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℂ) (k : ℕ), AnalyticAt ℂ f 0 → f 0 = 0 → c ≠ 0 → 1 ≤ k →
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => f z - c * z ^ k)
      (fun z => z ^ (k + 1)) →
    ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), f (χ s) = c * s ^ k

/-- Application of only the generic monomial normal-form input. All implicit
coefficient extraction and error absorption are proved above. -/
theorem implicit_energy_exact_normal_form
    (externalNormalForm : AnalyticMonomialNormalFormPrinciple)
    (μ C : ℝ) (γ : ℂ) (k : ℕ) (Ω R : ℂ → ℂ)
    (hμ : 0 < μ) (hC : 0 ≤ C) (hγ : γ ≠ 0) (hk : 1 ≤ k)
    (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0)
    (heq : ∀ᶠ θ in 𝓝 (0 : ℂ), (μ : ℂ) * Ω θ + γ * θ ^ k + R θ = 0)
    (hR : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖R θ‖ ≤ C * (‖θ‖ ^ (k + 1) + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(γ / (μ : ℂ)) * s ^ k := by
  apply externalNormalForm Ω (-(γ / (μ : ℂ))) k hΩ hΩ0
  · exact neg_ne_zero.mpr (div_ne_zero hγ (by exact_mod_cast hμ.ne'))
  · exact hk
  · simpa only [neg_mul, sub_neg_eq_add] using
      implicit_energy_graph_jet μ C γ k Ω R hμ hC hk hΩ hΩ0 heq hR

/-- The computed quadratic/cubic scalar residual, together with the proved
nondegeneracy alternative, gives exactly the two possible monomial degrees. -/
theorem quadratic_or_cubic_energy_normal_form
    (externalNormalForm : AnalyticMonomialNormalFormPrinciple)
    (μ C : ℝ) (σ ψ : ℂ) (Ω : ℂ → ℂ) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hnd : σ ≠ 0 ∨ ψ ≠ 0) (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0)
    (hR : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(μ : ℂ) * Ω θ + σ * θ ^ 2 + ψ * θ ^ 3‖ ≤
        C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    (σ ≠ 0 ∧ ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(σ / (μ : ℂ)) * s ^ 2) ∨
    (σ = 0 ∧ ψ ≠ 0 ∧ ∃ χ : ℂ → ℂ, AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = -(ψ / (μ : ℂ)) * s ^ 3) := by
  by_cases hσ : σ = 0
  · right
    have hψ : ψ ≠ 0 := hnd.resolve_left (not_not_intro hσ)
    refine ⟨hσ, hψ, ?_⟩
    apply implicit_energy_exact_normal_form externalNormalForm μ C ψ 3 Ω
      (fun θ => -((μ : ℂ) * Ω θ + ψ * θ ^ 3)) hμ hC hψ (by norm_num) hΩ hΩ0
    · exact Filter.Eventually.of_forall fun θ => by ring
    · filter_upwards [hR] with θ ht
      simpa only [hσ, zero_mul, add_zero, norm_neg] using ht
  · left
    refine ⟨hσ, ?_⟩
    have hC' : 0 ≤ C + ‖ψ‖ := add_nonneg hC (norm_nonneg _)
    apply implicit_energy_exact_normal_form externalNormalForm μ (C + ‖ψ‖) σ 2 Ω
      (fun θ => -((μ : ℂ) * Ω θ + σ * θ ^ 2)) hμ hC' hσ (by norm_num) hΩ hΩ0
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

end NonSymmetricDyson.Full.Singularities
