import Dyson.Full.NonlinearAnalytic
import Dyson.Full.NonlinearRoots
import Dyson.Full.Singularities
import Dyson.Model

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

@[simp] theorem quadraticNonlinearity_eq_normalized
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q h ξ : ι → ℂ) :
    quadraticNonlinearity F p q h ξ =
      Singularities.normalizedNonlinearity F.toLinearMap p q h ξ := rfl

/-- The forcing in the local polynomial is exactly the spectral increment
plus the actual reciprocal residual of the perturbed vector. -/
theorem actual_normalized_residual
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ z : ℂ) (mτ g p q h : ι → ℂ)
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hm : BasicEstimates.IsDysonSolution S a τ mτ)
    (hm0 : ∀ i, mτ i ≠ 0) (hg0 : ∀ i, g i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * mτ i)
    (hgm : g = mτ + q * h) :
    h - F h = quadraticNonlinearity F p q h
      (fun i => z - τ + Model.residual S a z g i) := by
  have hg : ∀ i, -(g i)⁻¹ = (τ - (a i : ℂ)) + Model.action S g i +
      (z - τ + Model.residual S a z g i) := by
    intro i
    simp only [Model.residual]
    ring
  have he := DysonPaper.Algebra.normalized_quadratic_equation mτ g
    (fun i => τ - (a i : ℂ)) (fun i => z - τ + Model.residual S a z g i)
    p q h (Model.action S) hm0 hg0 hq0 hp hq hgm hm hg
  simpa only [← hF, quadraticNonlinearity_eq_normalized,
    Singularities.normalizedNonlinearity] using he

/-- Full local Lyapunov--Schmidt equivalence for the constructed stable map.
Both directions are proved from the restricted inverse and its actual
fixed-point equation. -/
theorem local_reduction_equivalence
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r h ξ : ι → ℂ)
    (hFr : F r = r) (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hK : Singularities.IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (εw εp : ℝ)
    (hfixed : ∀ v, ‖v‖ < εp → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (huniq : ∀ w v, ‖w‖ < εw → ‖v‖ < εp →
      (w = K (quadraticNonlinearity F p q (v.1 • r + w) v.2) ↔ w = W v))
    (hsmallw : ‖h - ℓ h • r‖ < εw) (hsmallp : ‖(ℓ h, ξ)‖ < εp) :
    h - F h = quadraticNonlinearity F p q h ξ ↔
      h = ℓ h • r + W (ℓ h, ξ) ∧ reducedScalar F ℓ p q r W (ℓ h, ξ) = 0 := by
  have hpj := Singularities.projected_residual_iff F.toLinearMap K.toLinearMap ℓ.toLinearMap
    r h (quadraticNonlinearity F p q h ξ) hlF hK.kill_right hFr hK.left_inverse hK.right_inverse
  constructor
  · intro he
    obtain ⟨hh, hn⟩ := hpj.mp he
    change h = ℓ h • r + K (quadraticNonlinearity F p q h ξ) at hh
    have hw : h - ℓ h • r = K (quadraticNonlinearity F p q h ξ) := by
      calc
        _ = (ℓ h • r + K (quadraticNonlinearity F p q h ξ)) - ℓ h • r :=
          congrArg (fun v => v - ℓ h • r) hh
        _ = _ := by abel
    have hwp : h - ℓ h • r =
        K (quadraticNonlinearity F p q (ℓ h • r + (h - ℓ h • r)) ξ) := by
      convert hw using 2 <;> abel
    have hW := (huniq (h - ℓ h • r) (ℓ h, ξ) hsmallw hsmallp).mp hwp
    have hrec : h = ℓ h • r + W (ℓ h, ξ) := by rw [← hW]; abel
    refine ⟨hrec, ?_⟩
    change ℓ (quadraticNonlinearity F p q (ℓ h • r + W (ℓ h, ξ)) ξ) = 0
    rw [← hrec]
    exact hn
  · rintro ⟨hrec, hf⟩
    apply hpj.mpr
    constructor
    · have hw := hfixed (ℓ h, ξ) hsmallp
      change W (ℓ h, ξ) = K (quadraticNonlinearity F p q (ℓ h • r + W (ℓ h, ξ)) ξ) at hw
      rw [← hrec] at hw
      exact hrec.trans (congrArg (fun v => ℓ h • r + v) hw)
    · change ℓ (quadraticNonlinearity F p q (ℓ h • r + W (ℓ h, ξ)) ξ) = 0 at hf
      rwa [← hrec] at hf

/-- Scalar Taylor expansion after the actual forcing specialization
`ξ = ω·1`. In particular the linear spectral coefficient is exactly `ℓ q`. -/
theorem actual_spectral_taylor_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (hfixed : ∀ v, ‖v‖ < ε → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (hsize : ∀ v, ‖v‖ < ε → ‖W v‖ ≤ C * (‖v.1‖ ^ 2 + ‖v.2‖)) :
    ∃ δ > 0, ∃ B > 0, ∀ θ ω : ℂ, ‖θ‖ < δ → ‖ω‖ < δ →
      ‖spectralScalar F ℓ p q r W (θ, ω) - θ ^ 2 * ℓ (p * r * r) -
        θ ^ 3 * ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) - ℓ q * ω‖ ≤
        B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) := by
  obtain ⟨δ, hδ, B, hB, ht⟩ := stable_map_scalar_taylor_bound F K ℓ p q r hFr W ε C hε hC hfixed hsize
  refine ⟨δ, hδ, B, hB, ?_⟩
  intro θ ω hθ hω
  have hξ : ‖ω • (1 : ι → ℂ)‖ ≤ ‖ω‖ := by
    rw [norm_smul]
    have hone : ‖(1 : ι → ℂ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
    nlinarith [norm_nonneg ω]
  have hv : ‖(θ, ω • (1 : ι → ℂ))‖ < δ := by
    rw [Prod.norm_def]
    exact max_lt hθ (hξ.trans_lt hω)
  have hforce : ℓ (q * (ω • (1 : ι → ℂ))) = ℓ q * ω := by
    have he : q * (ω • (1 : ι → ℂ)) = ω • q := by
      ext i
      simp only [Pi.mul_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      ring
    rw [he, map_smul, smul_eq_mul, mul_comm]
  have h := ht (θ, ω • (1 : ι → ℂ)) hv
  simp only [Prod.fst, Prod.snd, hforce] at h
  exact h.trans (by gcongr)

theorem quadratic_leading_remainder_bound
    (f σ ψ μ θ ω : ℂ) (B : ℝ) (hB : 0 ≤ B) (hθ : ‖θ‖ ≤ 1)
    (hbase : ‖f - θ ^ 2 * σ - θ ^ 3 * ψ - μ * ω‖ ≤
      B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2)) :
    ‖f - σ * θ ^ 2 - μ * ω‖ ≤
      (B + ‖ψ‖) * (‖θ‖ ^ 3 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) := by
  have hT4 : ‖θ‖ ^ 4 ≤ ‖θ‖ ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hθ (pow_nonneg (norm_nonneg θ) 3)]
  have he : f - σ * θ ^ 2 - μ * ω =
      (f - θ ^ 2 * σ - θ ^ 3 * ψ - μ * ω) + θ ^ 3 * ψ := by ring
  rw [he]
  calc
    _ ≤ ‖f - θ ^ 2 * σ - θ ^ 3 * ψ - μ * ω‖ + ‖θ ^ 3 * ψ‖ := norm_add_le _ _
    _ ≤ B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) + ‖θ ^ 3 * ψ‖ := add_le_add_right hbase _
    _ = B * (‖θ‖ ^ 4 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) + ‖ψ‖ * ‖θ‖ ^ 3 := by
      rw [norm_mul, norm_pow]
      ring
    _ ≤ B * (‖θ‖ ^ 3 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) +
        ‖ψ‖ * (‖θ‖ ^ 3 + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by linarith) hB
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg ω), sq_nonneg ‖ω‖]
    _ = _ := by ring

/-- The nondegenerate quadratic/cubic alternatives produce exactly the
leading-term hypothesis required by the general analytic root argument. -/
theorem actual_spectral_leading_bound
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (hfixed : ∀ v, ‖v‖ < ε → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (hsize : ∀ v, ‖v‖ < ε → ‖W v‖ ≤ C * (‖v.1‖ ^ 2 + ‖v.2‖))
    (k : ℕ) (γ : ℂ)
    (hcase : (k = 2 ∧ γ = ℓ (p * r * r)) ∨
      (k = 3 ∧ ℓ (p * r * r) = 0 ∧
        γ = ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))))) :
    ∃ δ > 0, ∃ B > 0, ∀ θ ω : ℂ, ‖θ‖ < δ → ‖ω‖ < δ →
      ‖spectralScalar F ℓ p q r W (θ, ω) - γ * θ ^ k - ℓ q * ω‖ ≤
        B * (‖θ‖ ^ (k + 1) + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2) := by
  obtain ⟨δ, hδ, B, hB, ht⟩ := actual_spectral_taylor_bound F K ℓ p q r hFr W ε C hε hC hfixed hsize
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, hσ, rfl⟩
  · refine ⟨min δ 1, lt_min hδ zero_lt_one,
      B + ‖ℓ (p * r * (F (K (p * r * r)) + K (p * r * r)))‖, by positivity, ?_⟩
    intro θ ω hθ hω
    exact quadratic_leading_remainder_bound _ _ _ _ θ ω B hB.le
      (hθ.le.trans (min_le_right _ _))
      (ht θ ω (hθ.trans_le (min_le_left _ _)) (hω.trans_le (min_le_left _ _)))
  · refine ⟨δ, hδ, B, hB, ?_⟩
    intro θ ω hθ hω
    have h := ht θ ω hθ hω
    rw [hσ, mul_zero, sub_zero] at h
    simpa only [mul_comm] using h

/-- Application of the generic analytic root argument to the scalar function
actually obtained from the Dyson polynomial. Analyticity, leading coefficients,
and the quantitative remainder hypothesis have all been proved above. -/
theorem actual_spectral_root_factorization
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (hWa : AnalyticAt ℂ W 0)
    (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (hfixed : ∀ v, ‖v‖ < ε → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (hsize : ∀ v, ‖v‖ < ε → ‖W v‖ ≤ C * (‖v.1‖ ^ 2 + ‖v.2‖))
    (k : ℕ) (γ : ℂ) (hγ : γ ≠ 0) (hμ : ℓ q ≠ 0)
    (hcase : (k = 2 ∧ γ = ℓ (p * r * r)) ∨
      (k = 3 ∧ ℓ (p * r * r) = 0 ∧
        γ = ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))))) :
    ∃ ρ > 0, ∃ δ > 0, ∃ c > 0, ∃ Croot > 0, ∃ roots : Fin k → ℂ → ℂ,
      (∀ j, ContinuousOn (roots j) {ω | 0 < ω.im ∧ ‖ω‖ < δ}) ∧
      (∀ ω, 0 < ω.im → ‖ω‖ < δ →
        (∀ j, spectralScalar F ℓ p q r W (roots j ω, ω) = 0 ∧
          c * ‖ω‖ ^ ((1 : ℝ) / k) ≤ ‖roots j ω‖ ∧
          ‖roots j ω‖ ≤ Croot * ‖ω‖ ^ ((1 : ℝ) / k)) ∧
        (∀ i j, i ≠ j → c * ‖ω‖ ^ ((1 : ℝ) / k) ≤ ‖roots i ω - roots j ω‖) ∧
        (∀ θ, ‖θ‖ ≤ ρ →
          c * (∏ j, ‖θ - roots j ω‖) ≤ ‖spectralScalar F ℓ p q r W (θ, ω)‖ ∧
          ‖spectralScalar F ℓ p q r W (θ, ω)‖ ≤ Croot * (∏ j, ‖θ - roots j ω‖))) := by
  have hk : 2 ≤ k := by rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  exact rootArgument k hk (spectralScalar F ℓ p q r W) γ (ℓ q)
    (spectralScalar_analytic F ℓ p q r W hWa) hγ hμ
    (actual_spectral_leading_bound F K ℓ p q r hFr W ε C hε hC hfixed hsize k γ hcase)

end NonSymmetricDyson.Full.Nonlinear
