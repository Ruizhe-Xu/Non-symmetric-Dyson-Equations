import Dyson.Full.NonlinearAnalytic
import Dyson.Full.PowerGluing

noncomputable section

namespace NonSymmetricDyson.Full.Nonlinear

/-- Absorption of the exact mixed Taylor remainder, retaining the explicit
smallness scale of the leading coefficient. -/
theorem rough_scalar_from_mixed_remainder
    (γ θ a : ℂ) (k : ℕ) (X A B : ℝ)
    (hγ : γ ≠ 0) (hX : 0 ≤ X) (hX1 : X ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : ‖θ‖ ≤ 1)
    (hsmall : 2 * B * ‖θ‖ ≤ ‖γ‖)
    (ha : ‖a‖ ≤ A * X)
    (herr : ‖γ * θ ^ k + a‖ ≤ B * (‖θ‖ ^ (k + 1) + ‖θ‖ * X + X ^ 2)) :
    ‖θ‖ ^ k ≤ (2 * (A + 2 * B) / ‖γ‖) * X := by
  have hγpos := norm_pos_iff.mpr hγ
  have hpure := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (norm_nonneg θ) k)
  have hmixed : ‖θ‖ * X + X ^ 2 ≤ 2 * X := by nlinarith [norm_nonneg θ]
  have hnorm : ‖γ‖ * ‖θ‖ ^ k ≤ ‖γ * θ ^ k + a‖ + ‖a‖ := by
    calc
      _ = ‖γ * θ ^ k‖ := by rw [norm_mul, norm_pow]
      _ = ‖(γ * θ ^ k + a) - a‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hbound := hnorm.trans (add_le_add herr ha)
  have hmixed' := mul_le_mul_of_nonneg_left hmixed hB
  rw [pow_succ] at hbound
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hγpos).mpr
  nlinarith

/-- Elementary power bounds for the two possible boundary degrees. -/
theorem two_or_three_sum_power_bound
    (k : ℕ) (hk : k = 2 ∨ k = 3) (T X : ℝ) (hT : 0 ≤ T) (hX : 0 ≤ X) :
    (T + X) ^ k ≤ (2 : ℝ) ^ (k - 1) * (T ^ k + X ^ k) := by
  rcases hk with rfl | rfl
  · norm_num
    nlinarith [sq_nonneg (T - X)]
  · norm_num
    nlinarith [mul_nonneg (sq_nonneg (T - X)) (add_nonneg hT hX)]

/-- The actual normalized vector inherits the rough scalar power bound.
All constants are displayed and no branch information is used. -/
theorem rough_vector_power_bound
    {ι : Type*} [Fintype ι] (r w : ι → ℂ) (θ : ℂ)
    (k : ℕ) (hk : k = 2 ∨ k = 3) (X C D : ℝ)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ‖θ‖ ≤ 1) (hscalar : ‖θ‖ ^ k ≤ C * X)
    (hstable : ‖w‖ ≤ D * (‖θ‖ ^ 2 + X)) :
    ‖θ • r + w‖ ^ k ≤
      (‖r‖ + D) ^ k * (2 : ℝ) ^ (k - 1) * (C + 1) * X := by
  have hθ2 : ‖θ‖ ^ 2 ≤ ‖θ‖ := by nlinarith [norm_nonneg θ]
  have hnorm : ‖θ • r + w‖ ≤ (‖r‖ + D) * (‖θ‖ + X) := by
    calc
      _ ≤ ‖θ‖ * ‖r‖ + ‖w‖ := by simpa only [norm_smul] using norm_add_le (θ • r) w
      _ ≤ ‖θ‖ * ‖r‖ + D * (‖θ‖ ^ 2 + X) := add_le_add_left hstable _
      _ ≤ ‖θ‖ * ‖r‖ + D * (‖θ‖ + X) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg r) hX]
  have hXp : X ^ k ≤ X := by
    rcases hk with rfl | rfl
    · nlinarith
    · have hX2 : X ^ 2 ≤ X := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hX2 hX]
  calc
    _ ≤ ((‖r‖ + D) * (‖θ‖ + X)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hnorm _
    _ = (‖r‖ + D) ^ k * (‖θ‖ + X) ^ k := mul_pow _ _ _
    _ ≤ (‖r‖ + D) ^ k * ((2 : ℝ) ^ (k - 1) * (‖θ‖ ^ k + X ^ k)) :=
      mul_le_mul_of_nonneg_left (two_or_three_sum_power_bound k hk ‖θ‖ X (norm_nonneg _) hX)
        (by positivity)
    _ ≤ (‖r‖ + D) ^ k * ((2 : ℝ) ^ (k - 1) * (C * X + X)) := by gcongr
    _ = _ := by ring

/-- The two nondegenerate alternatives turn the computed scalar Taylor
expansion into its leading monomial estimate. -/
theorem leading_from_full_taylor_bound
    (σ ψ θ a γ : ℂ) (k : ℕ)
    (hcase : (k = 2 ∧ γ = σ) ∨ (k = 3 ∧ σ = 0 ∧ γ = ψ))
    (B X : ℝ) (hB : 0 ≤ B) (hX : 0 ≤ X) (hθ : ‖θ‖ ≤ 1)
    (hfull : ‖θ ^ 2 * σ + θ ^ 3 * ψ + a‖ ≤
      B * (‖θ‖ ^ 4 + ‖θ‖ * X + X ^ 2)) :
    ‖γ * θ ^ k + a‖ ≤
      (B + ‖ψ‖) * (‖θ‖ ^ (k + 1) + ‖θ‖ * X + X ^ 2) := by
  rcases hcase with ⟨hk, hg⟩ | ⟨hk, hσ, hg⟩
  · subst k
    rw [hg]
    have hT4 : ‖θ‖ ^ 4 ≤ ‖θ‖ ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hθ (pow_nonneg (norm_nonneg θ) 3)]
    have he : σ * θ ^ 2 + a = (θ ^ 2 * σ + θ ^ 3 * ψ + a) - θ ^ 3 * ψ := by ring
    rw [he]
    calc
      _ ≤ ‖θ ^ 2 * σ + θ ^ 3 * ψ + a‖ + ‖θ ^ 3 * ψ‖ := norm_sub_le _ _
      _ ≤ B * (‖θ‖ ^ 4 + ‖θ‖ * X + X ^ 2) + ‖θ ^ 3 * ψ‖ := add_le_add_right hfull _
      _ = B * (‖θ‖ ^ 4 + ‖θ‖ * X + X ^ 2) + ‖ψ‖ * ‖θ‖ ^ 3 := by rw [norm_mul, norm_pow]; ring
      _ ≤ B * (‖θ‖ ^ 3 + ‖θ‖ * X + X ^ 2) +
          ‖ψ‖ * (‖θ‖ ^ 3 + ‖θ‖ * X + X ^ 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by linarith) hB
        · exact mul_le_mul_of_nonneg_left
            (by nlinarith [mul_nonneg (norm_nonneg θ) hX, sq_nonneg X]) (norm_nonneg _)
      _ = _ := by ring
  · subst k
    rw [hg]
    rw [hσ, mul_zero, zero_add] at hfull
    have h : ‖ψ * θ ^ 3 + a‖ ≤ B * (‖θ‖ ^ 4 + ‖θ‖ * X + X ^ 2) := by
      simpa only [mul_comm] using hfull
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [norm_nonneg ψ]) (by positivity))

/-- A rough scalar estimate is derived for every actual sufficiently small
stable fixed point satisfying the scalar equation. -/
theorem actual_rough_scalar_power_bound
    {ι : Type*} [Fintype ι]
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r) (k : ℕ) (γ : ℂ) (hγ : γ ≠ 0)
    (hcase : (k = 2 ∧ γ = ℓ (p * r * r)) ∨
      (k = 3 ∧ ℓ (p * r * r) = 0 ∧
        γ = ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))))) :
    ∃ c > 0, ∃ C > 0, ∀ (θ : ℂ) (w ξ : ι → ℂ),
      w = K (quadraticNonlinearity F p q (θ • r + w) ξ) →
      ‖θ • r + w‖ ≤ 1 → 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖w‖ ≤ 1 →
      ‖θ‖ ≤ c → ‖ξ‖ ≤ c → ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) = 0 →
      ‖θ‖ ^ k ≤ C * ‖ξ‖ := by
  obtain ⟨B, hB, hTaylor⟩ := fixed_point_uniform_scalar_taylor F K ℓ p q r hFr
  let ψ := ℓ (p * r * (F (K (p * r * r)) + K (p * r * r)))
  let B' := B + ‖ψ‖
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hγpos : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  let A := ‖ℓ‖ * ‖q‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨min 1 (‖γ‖ / (2 * B')), lt_min zero_lt_one (by positivity),
    2 * (A + 2 * B') / ‖γ‖, by positivity, ?_⟩
  intro θ w ξ hw hlocal hsmall hθ hξ hzero
  have hθ1 : ‖θ‖ ≤ 1 := hθ.trans (min_le_left _ _)
  have hξ1 : ‖ξ‖ ≤ 1 := hξ.trans (min_le_left _ _)
  have hθsmall : 2 * B' * ‖θ‖ ≤ ‖γ‖ := by
    have h := (le_div_iff₀ (show 0 < 2 * B' by positivity)).mp (hθ.trans (min_le_right _ _))
    nlinarith
  have ht := hTaylor θ w ξ hw hlocal hsmall hθ1 hξ1
  rw [hzero] at ht
  have hfull : ‖θ ^ 2 * ℓ (p * r * r) + θ ^ 3 * ψ + ℓ (q * ξ)‖ ≤
      B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
    have he : (0 : ℂ) - θ ^ 2 * ℓ (p * r * r) - θ ^ 3 * ψ - ℓ (q * ξ) =
        -(θ ^ 2 * ℓ (p * r * r) + θ ^ 3 * ψ + ℓ (q * ξ)) := by ring
    rw [he, norm_neg] at ht
    exact ht
  have ha : ‖ℓ (q * ξ)‖ ≤ A * ‖ξ‖ := by
    calc
      _ ≤ ‖ℓ‖ * ‖q * ξ‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (‖q‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ = _ := by dsimp [A]; ring
  exact rough_scalar_from_mixed_remainder γ θ (ℓ (q * ξ)) k ‖ξ‖ A B' hγ
    (norm_nonneg ξ) hξ1 hA hB'.le hθ1 hθsmall ha
    (leading_from_full_taylor_bound _ ψ θ _ γ k hcase B ‖ξ‖ hB.le (norm_nonneg ξ) hθ1 hfull)

/-- The actual local nonlinear equation satisfies the expected rough
Hölder estimate of degree two or three, with one fixed neighborhood. -/
theorem actual_rough_vector_root_bound
    {ι : Type*} [Fintype ι]
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r) (k : ℕ) (γ : ℂ) (hγ : γ ≠ 0)
    (hcase : (k = 2 ∧ γ = ℓ (p * r * r)) ∨
      (k = 3 ∧ ℓ (p * r * r) = 0 ∧
        γ = ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))))) :
    ∃ c > 0, ∃ C > 0, ∀ (θ : ℂ) (w ξ : ι → ℂ),
      w = K (quadraticNonlinearity F p q (θ • r + w) ξ) →
      ‖θ • r + w‖ ≤ 1 → 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖w‖ ≤ 1 →
      ‖θ‖ ≤ c → ‖ξ‖ ≤ c → ℓ (quadraticNonlinearity F p q (θ • r + w) ξ) = 0 →
      ‖θ • r + w‖ ≤ C * ‖ξ‖ ^ ((1 : ℝ) / k) := by
  obtain ⟨c, hc, A, hA, hscalar⟩ := actual_rough_scalar_power_bound F K ℓ p q r hFr k γ hγ hcase
  have hk : k = 2 ∨ k = 3 := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hkpos : 0 < k := by rcases hk with rfl | rfl <;> omega
  let a := 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2
  let b := 2 * ‖K‖ * ‖q‖ * (1 + ‖p‖)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let D := 1 + a + b
  have hD : 0 < D := by dsimp [D]; positivity
  let B := (‖r‖ + D) ^ k * (2 : ℝ) ^ (k - 1) * (A + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨min c 1, lt_min hc zero_lt_one, B ^ ((1 : ℝ) / k), Real.rpow_pos_of_pos hB _, ?_⟩
  intro θ w ξ hw hlocal hsmall hθ hξ hzero
  have hθ1 := hθ.trans (min_le_right _ _)
  have hξ1 := hξ.trans (min_le_right _ _)
  have hsp := hscalar θ w ξ hw hlocal hsmall (hθ.trans (min_le_left _ _))
    (hξ.trans (min_le_left _ _)) hzero
  have hstable : ‖w‖ ≤ D * (‖θ‖ ^ 2 + ‖ξ‖) := by
    have hh : ‖w‖ ≤ a * ‖θ‖ ^ 2 + b * ‖ξ‖ := stable_fixed_point_size F K p q r w ξ θ hw hlocal hsmall
    calc
      _ ≤ a * ‖θ‖ ^ 2 + b * ‖ξ‖ := hh
      _ ≤ D * ‖θ‖ ^ 2 + D * ‖ξ‖ := by gcongr <;> dsimp [D] <;> linarith
      _ = _ := by ring
  exact PowerGluing.nonnegative_power_bound_to_root (norm_nonneg _) hB.le (norm_nonneg ξ) k hkpos
    (rough_vector_power_bound r w θ k hk ‖ξ‖ A D (norm_nonneg ξ) hξ1 hA.le hD.le hθ1 hsp hstable)

end NonSymmetricDyson.Full.Nonlinear
