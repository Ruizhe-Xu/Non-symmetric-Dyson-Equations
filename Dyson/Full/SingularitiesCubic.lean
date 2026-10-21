import Dyson.Full.SingularitiesChart

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- A universal classical analytic estimate: a real holomorphic germ
vanishing to order at least n has imaginary part bounded by
C|z|^(n-1)|Im z|. This is the vertical mean-value estimate for its derivative;
it contains no Dyson data, curve, residual, or density conclusion. -/
def RealAnalyticImaginaryOrderBoundPrinciple : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ), 1 ≤ n → AnalyticAt ℂ f 0 → RealAnalyticGerm f →
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) f (fun z => z ^ n) →
    ∃ C > 0, ∀ᶠ z in 𝓝 (0 : ℂ), |(f z).im| ≤ C * ‖z‖ ^ (n - 1) * |z.im|

/-- A holomorphic coordinate normalized by χ'(0)=1 is quantitatively
comparable with the identity. The estimate follows from the checked
quadratic Taylor remainder. -/
theorem normalized_coordinate_norm_comparison (χ : ℂ → ℂ)
    (ha : AnalyticAt ℂ χ 0) (h0 : χ 0 = 0) (hd : HasDerivAt χ 1 0) :
    ∀ᶠ s in 𝓝 (0 : ℂ), ‖χ s‖ ≤ 2 * ‖s‖ ∧ ‖s‖ ≤ 2 * ‖χ s‖ := by
  obtain ⟨C, hC, ht⟩ := analytic_quadratic_taylor_bound χ 1 ha hd
  have hs : ∀ᶠ s : ℂ in 𝓝 0, C * ‖s‖ ≤ 1 / 2 := by
    have hh := (continuousAt_const.mul continuousAt_id.norm).eventually_lt continuousAt_const
      (show C * ‖(0 : ℂ)‖ < (1 : ℝ) / 2 by simp)
    exact hh.mono fun _ h => h.le
  filter_upwards [ht, hs] with s ht hs
  simp only [h0, sub_zero, smul_eq_mul, mul_one] at ht
  have herr : ‖χ s - s‖ ≤ ‖s‖ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hs (norm_nonneg s)
    nlinarith
  have hupper := norm_sub_le (χ s - s) (-s)
  have hlower := norm_sub_le (χ s) (χ s - s)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, sub_sub_cancel] at hupper hlower
  constructor <;> nlinarith [norm_nonneg s, norm_nonneg (χ s)]

/-- The exact monomial chart gives both parameter/energy power estimates
throughout a full neighborhood, not only along a chosen root. -/
theorem exact_normal_form_power_comparison (Ω χ : ℂ → ℂ) (c : ℂ) (k : ℕ)
    (hc : c ≠ 0) (hχa : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) (hχd : HasDerivAt χ 1 0)
    (hform : ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = c * s ^ k) :
    ∃ A > 0, ∃ B > 0, ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖θ‖ ^ k ≤ A * ‖Ω θ‖ ∧ ‖Ω θ‖ ≤ B * ‖θ‖ ^ k := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hsder : HasStrictDerivAt χ 1 0 := by
    have hh := hχa.hasStrictFDerivAt.hasStrictDerivAt
    simpa only [hh.hasDerivAt.unique hχd] using hh
  have hmap : Filter.map χ (𝓝 (0 : ℂ)) = 𝓝 0 := by
    simpa only [hχ0] using hsder.map_nhds_eq (by norm_num : (1 : ℂ) ≠ 0)
  refine ⟨2 ^ k / ‖c‖, div_pos (pow_pos (by norm_num) k) hcpos,
    ‖c‖ * 2 ^ k, mul_pos hcpos (pow_pos (by norm_num) k), ?_⟩
  rw [← hmap]
  change ∀ᶠ s in 𝓝 (0 : ℂ), _
  filter_upwards [hform, normalized_coordinate_norm_comparison χ hχa hχ0 hχd] with s hf hs
  have hn : ‖Ω (χ s)‖ = ‖c‖ * ‖s‖ ^ k := by rw [hf, norm_mul, norm_pow]
  constructor
  · calc
      ‖χ s‖ ^ k ≤ (2 * ‖s‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) hs.1 k
      _ = (2 ^ k / ‖c‖) * ‖Ω (χ s)‖ := by rw [hn, mul_pow]; field_simp
  · calc
      ‖Ω (χ s)‖ = ‖c‖ * ‖s‖ ^ k := hn
      _ ≤ ‖c‖ * (2 * ‖χ s‖) ^ k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hs.2 k) (norm_nonneg _)
      _ = (‖c‖ * 2 ^ k) * ‖χ s‖ ^ k := by rw [mul_pow]; ring

/-- Substituting the proved energy scale into the mixed Taylor error yields
order k+1 of the actual scalar residual along its analytic solution graph. -/
theorem scalar_graph_residual_order (Ω : ℂ → ℂ) (μ σ ψ C B : ℝ) (k : ℕ)
    (hC : 0 < C) (hB : 0 < B) (hk : k = 2 ∨ k = 3)
    (hscale : ∀ᶠ θ in 𝓝 (0 : ℂ), ‖Ω θ‖ ≤ B * ‖θ‖ ^ k)
    (hTaylor : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3‖ ≤
        C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun θ => (μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3)
      (fun θ => θ ^ (k + 1)) := by
  apply Asymptotics.IsBigO.of_bound (C * (1 + B + B ^ 2))
  have hsmall : ∀ᶠ θ : ℂ in 𝓝 0, ‖θ‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with θ hθ
    exact le_of_lt (by simpa using hθ)
  filter_upwards [hscale, hTaylor, hsmall] with θ hs ht hθ
  rw [norm_pow]
  have h₄ : ‖θ‖ ^ 4 ≤ ‖θ‖ ^ (k + 1) :=
    pow_le_pow_of_le_one (norm_nonneg _) hθ (by rcases hk with rfl | rfl <;> norm_num)
  have h₂k : ‖θ‖ ^ (2 * k) ≤ ‖θ‖ ^ (k + 1) :=
    pow_le_pow_of_le_one (norm_nonneg _) hθ (by rcases hk with rfl | rfl <;> norm_num)
  have hmix : ‖Ω θ‖ * ‖θ‖ ≤ B * ‖θ‖ ^ (k + 1) := by
    simpa only [pow_succ, mul_assoc] using mul_le_mul_of_nonneg_right hs (norm_nonneg θ)
  have hsq : ‖Ω θ‖ ^ 2 ≤ B ^ 2 * ‖θ‖ ^ (k + 1) := by
    calc
      ‖Ω θ‖ ^ 2 ≤ (B * ‖θ‖ ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
      _ = B ^ 2 * ‖θ‖ ^ (2 * k) := by rw [mul_pow, ← pow_mul]; congr 2; omega
      _ ≤ B ^ 2 * ‖θ‖ ^ (k + 1) := mul_le_mul_of_nonneg_left h₂k (sq_nonneg _)
  calc
    _ ≤ C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) := ht
    _ ≤ C * (‖θ‖ ^ (k + 1) + B * ‖θ‖ ^ (k + 1) + B ^ 2 * ‖θ‖ ^ (k + 1)) := by gcongr
    _ = _ := by ring

/-- The literal scalar and imaginary error estimates in the manuscript's
cubic proposition, obtained from the actual energy graph and its computed
coefficients. The only new external premise is the universal real-analytic
vanishing-order estimate stated above. -/
theorem scalar_graph_cubic_error
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    (Ω : ℂ → ℂ) (μ σ ψ C : ℝ) (hμ : 0 < μ) (hC : 0 < C)
    (hΩ : AnalyticAt ℂ Ω 0) (hΩ0 : Ω 0 = 0) (hΩreal : RealAnalyticGerm Ω)
    (hnd : σ ≠ 0 ∨ 0 < ψ)
    (hTaylor : ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3‖ ≤
        C * (‖θ‖ ^ 4 + ‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2)) :
    ∃ B > 0, ∀ᶠ θ in 𝓝 (0 : ℂ),
      ‖(μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3‖ ≤
        B * (‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) ∧
      |((μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3).im| ≤
        B * ‖Ω θ‖ * |θ.im| := by
  have hndC : (σ : ℂ) ≠ 0 ∨ (ψ : ℂ) ≠ 0 := by
    rcases hnd with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h.ne')
  obtain hforms := quadratic_or_cubic_real_energy_normal_form normalForm μ C
    (σ : ℂ) (ψ : ℂ) Ω hμ hC.le hndC hΩ hΩ0 hΩreal (by simp) (by simp) hTaylor
  have hchart : ∃ k : ℕ, ∃ c : ℂ, ∃ χ : ℂ → ℂ,
      (k = 2 ∨ k = 3) ∧ c ≠ 0 ∧ AnalyticAt ℂ χ 0 ∧ χ 0 = 0 ∧ HasDerivAt χ 1 0 ∧
        ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = c * s ^ k := by
    rcases hforms with ⟨hs, χ, ha, h0, hd, _, hf⟩ | ⟨_, hs, χ, ha, h0, hd, _, hf⟩
    · exact ⟨2, -((σ : ℂ) / μ), χ, Or.inl rfl,
        neg_ne_zero.mpr (div_ne_zero hs (by exact_mod_cast hμ.ne')), ha, h0, hd, hf⟩
    · exact ⟨3, -((ψ : ℂ) / μ), χ, Or.inr rfl,
        neg_ne_zero.mpr (div_ne_zero hs (by exact_mod_cast hμ.ne')), ha, h0, hd, hf⟩
  obtain ⟨k, c, χ, hk, hc, hχa, hχ0, hχd, hf⟩ := hchart
  obtain ⟨A, hA, D, hD, hscale⟩ := exact_normal_form_power_comparison Ω χ c k hc hχa hχ0 hχd hf
  let e : ℂ → ℂ := fun θ => (μ : ℂ) * Ω θ + (σ : ℂ) * θ ^ 2 + (ψ : ℂ) * θ ^ 3
  have heO := scalar_graph_residual_order Ω μ σ ψ C D k hC hD hk
    (hscale.mono fun _ h => h.2) hTaylor
  have hea : AnalyticAt ℂ e 0 :=
    (analyticAt_const.mul hΩ |>.add (analyticAt_const.mul (analyticAt_id.pow 2))).add
      (analyticAt_const.mul (analyticAt_id.pow 3))
  have hereal : RealAnalyticGerm e := by
    filter_upwards [hΩreal] with θ hθ
    change Ω ((starRingEnd ℂ) θ) = (starRingEnd ℂ) (Ω θ) at hθ
    simp [e, hθ]
  obtain ⟨E, hE, he⟩ := heO.exists_pos
  obtain ⟨J, hJ, hi⟩ := imaginaryOrder e (k + 1) (by omega) hea hereal heO
  let B : ℝ := A * (E + J)
  have hB : 0 < B := mul_pos hA (add_pos hE hJ)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hscale, he.bound, hi] with θ hs he hi
  change ‖e θ‖ ≤ E * ‖θ ^ (k + 1)‖ at he
  rw [norm_pow, pow_succ] at he
  simp only [Nat.add_sub_cancel] at hi
  constructor
  · calc
      ‖e θ‖ ≤ E * (‖θ‖ ^ k * ‖θ‖) := he
      _ ≤ E * (A * ‖Ω θ‖ * ‖θ‖) := by gcongr; exact hs.1
      _ ≤ B * (‖Ω θ‖ * ‖θ‖ + ‖Ω θ‖ ^ 2) := by
        dsimp [B]
        nlinarith [mul_nonneg hA.le (mul_nonneg hJ.le (mul_nonneg (norm_nonneg (Ω θ)) (norm_nonneg θ))),
          mul_nonneg (mul_nonneg hA.le (add_nonneg hE.le hJ.le)) (sq_nonneg ‖Ω θ‖)]
  · calc
      |(e θ).im| ≤ J * ‖θ‖ ^ k * |θ.im| := hi
      _ ≤ J * (A * ‖Ω θ‖) * |θ.im| := by gcongr; exact hs.1
      _ ≤ B * ‖Ω θ‖ * |θ.im| := by
        dsimp [B]
        nlinarith [mul_nonneg (mul_nonneg hA.le hE.le)
          (mul_nonneg (norm_nonneg (Ω θ)) (abs_nonneg θ.im))]

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Literal cubic error and leading-vector estimates for every sufficiently
small exact normalized Dyson solution, with the coefficients computed by the
restricted inverse. Local uniqueness transfers the analytic graph estimates
to all such solutions. -/
theorem normalized_cubic_error_neighborhood
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
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
    ∃ B > 0, ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 0,
      v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
      ‖v.2 - ℓ v.2 • r‖ ≤ B * (‖ℓ v.2‖ ^ 2 + ‖v.1‖) ∧
      ‖(μ : ℂ) * v.1 + (σ : ℂ) * (ℓ v.2) ^ 2 + (ψ : ℂ) * (ℓ v.2) ^ 3‖ ≤
        B * (‖v.1‖ * ‖ℓ v.2‖ + ‖v.1‖ ^ 2) ∧
      |((μ : ℂ) * v.1 + (σ : ℂ) * (ℓ v.2) ^ 2 + (ψ : ℂ) * (ℓ v.2) ^ 3).im| ≤
        B * ‖v.1‖ * |(ℓ v.2).im| := by
  have hμ : ℓ q ≠ 0 := by rw [hμeq]; exact_mod_cast hμpos.ne'
  obtain ⟨curve, hca, hc0, hc, hu, C, hC, ht⟩ :=
    exists_energy_curve_with_scalar_taylor_and_uniqueness F K ℓ p q r hμ hFr hlF hsimple hK
  have href := normalized_curve_reflection F ℓ p q hFreal hℓreal hp hq curve hca hc0 hc hu
  have hΩa : AnalyticAt ℂ (fun θ => (curve θ).1) 0 :=
    ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt _).comp hca
  have hΩreal : RealAnalyticGerm (fun θ => (curve θ).1) := by
    filter_upwards [href] with θ hθ
    exact congrArg Prod.fst hθ
  obtain ⟨B, hB, hb⟩ := scalar_graph_cubic_error normalForm imaginaryOrder
    (fun θ => (curve θ).1) μ σ ψ C hμpos hC hΩa (by simp [hc0]) hΩreal hnd
    (by simpa only [hμeq, hσ, hψ] using ht)
  have hd := normalized_solution_curve_tangent F ℓ p q r hμ hFr hnorm hlF hsimple curve hca hc0 hc
  have hHa : AnalyticAt ℂ (fun θ => (curve θ).2) 0 :=
    ((ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)).analyticAt _).comp hca
  obtain ⟨A, hA, ha⟩ := analytic_quadratic_taylor_bound (fun θ => (curve θ).2) r hHa hd.snd
  have hlt : Tendsto (fun v : ℂ × (ι → ℂ) => ℓ v.2) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun v : ℂ × (ι → ℂ) => ℓ v.2) := ℓ.continuous.comp continuous_snd
    simpa using hcont.continuousAt.tendsto (x := (0 : ℂ × (ι → ℂ)))
  refine ⟨A + B, add_pos hA hB, ?_⟩
  filter_upwards [hu, hlt.eventually hb, hlt.eventually ha] with v hu hb ha hres
  have hv := hu hres
  rw [hv] at hb
  simp only [hc0, Prod.snd_zero, sub_zero] at ha
  rw [hv] at ha
  refine ⟨?_, ?_, ?_⟩
  · exact ha.trans (by
      nlinarith [mul_nonneg hB.le (sq_nonneg ‖ℓ v.2‖),
        mul_nonneg (add_nonneg hA.le hB.le) (norm_nonneg v.1)])
  · exact hb.1.trans (by gcongr; linarith)
  · exact hb.2.trans (by gcongr; linarith)

end NonSymmetricDyson.Full.Singularities
