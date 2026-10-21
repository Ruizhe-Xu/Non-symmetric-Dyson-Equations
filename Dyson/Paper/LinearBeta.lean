import Dyson.Full.SpectralConsequences

/-! The non-cancellation step in the original M6 proof.  It uses the real
and imaginary parts of the actual spectral Taylor polynomial. -/
noncomputable section
namespace NonSymmetricDyson.Paper.LinearBeta

def model (a σ ψ δ : ℝ) : ℂ :=
  (a:ℂ)-2*Complex.I*(σ:ℂ)*(δ:ℂ)+2*((ψ-σ^2:ℝ):ℂ)*(δ:ℂ)^2

theorem coordinate_estimates {β : ℂ} {a σ ψ δ R : ℝ}
    (he : ‖β-model a σ ψ δ‖≤R) :
    |β.re-(a+2*(ψ-σ^2)*δ^2)|≤R ∧ |β.im+2*σ*δ|≤R := by
  constructor
  · simpa [model, pow_two] using (Complex.abs_re_le_norm (β-model a σ ψ δ)).trans he
  · simpa [model, pow_two] using (Complex.abs_im_le_norm (β-model a σ ψ δ)).trans he

/-- Positivity of ψ and σ²+ψ prevents cancellation between the real and
imaginary leading terms.  The negative real term −2σ²δ² is absorbed using
the imaginary term, not discarded. -/
theorem positive_model_lower {β : ℂ} {a σ ψ δ b R : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hψ : 0≤ψ) (hb : 0<b)
    (hnd : b≤σ^2+ψ) (hsmall : |σ| *δ≤1)
    (he : ‖β-model a σ ψ δ‖≤R)
    (hR : R≤(min 1 b/8)*(a+δ^2)) :
    (min 1 b/8)*(a+δ^2)≤‖β‖ := by
  obtain ⟨hre,him⟩ := coordinate_estimates he
  have hN : 0≤‖β‖ := norm_nonneg _
  have hR0 : 0≤R := (norm_nonneg _).trans he
  have hr := abs_le.mp (Complex.abs_re_le_norm β)
  have hi := abs_le.mp (Complex.abs_im_le_norm β)
  have hrr := abs_le.mp hre
  have hii := abs_le.mp him
  have himag : 2*|σ| *δ≤‖β‖+R := by
    rcases le_total 0 σ with hs|hs
    · rw [abs_of_nonneg hs]
      linarith
    · rw [abs_of_nonpos hs]
      linarith
  have hsquare : 2*σ^2*δ^2≤‖β‖+R := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0≤2*|σ| *δ by positivity)
    nlinarith [sq_abs σ]
  have hreal : a+2*ψ*δ^2≤2*(‖β‖+R) := by nlinarith
  have ha' : a≤2*(‖β‖+R) := by nlinarith [mul_nonneg hψ (sq_nonneg δ)]
  have hb' : b*δ^2≤2*(‖β‖+R) := by
    have hh := mul_le_mul_of_nonneg_right hnd (sq_nonneg δ)
    nlinarith
  have hmpos : 0< min 1 b := lt_min (by norm_num) hb
  have hma := mul_le_mul_of_nonneg_right (min_le_left 1 b) ha
  have hmb := mul_le_mul_of_nonneg_right (min_le_right 1 b) (sq_nonneg δ)
  nlinarith

/-- The manuscript remainder O(δ³+η) is absorbed because the exact Perron
identity gives μη=aδ and μ has a positive lower bound. -/
theorem absorb_spectral_remainder {a δ η μ c C b : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hη : 0≤η) (hc : 0<c) (hμ : c≤μ)
    (hidentity : μ*η=a*δ) (hC : 0≤C) (hb : 0<b)
    (hsmall : C*(1+c⁻¹)*δ≤ min 1 b/8) :
    C*(δ^3+η)≤(min 1 b/8)*(a+δ^2) := by
  have heta : η≤a*δ/c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hcoef : C*δ≤C*(1+c⁻¹)*δ := by
    have := mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hc.le)) hδ
    nlinarith
  have hcoeff : C*δ/c≤C*(1+c⁻¹)*δ := by
    rw [div_eq_mul_inv]
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right (hcoef.trans hsmall) (sq_nonneg δ)
  have h2 := mul_le_mul_of_nonneg_right (hcoeff.trans hsmall) ha
  have h3 := mul_le_mul_of_nonneg_left heta hC
  simp only [div_eq_mul_inv] at h2 h3 ⊢
  nlinarith

theorem beta_lower_from_original_expansion {β : ℂ} {a σ ψ δ η μ c C b : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hη : 0≤η) (hψ : 0≤ψ)
    (hc : 0<c) (hμ : c≤μ) (hidentity : μ*η=a*δ)
    (hC : 0≤C) (hb : 0<b) (hnd : b≤σ^2+ψ)
    (hsmallσ : |σ| *δ≤1) (hsmallδ : C*(1+c⁻¹)*δ≤ min 1 b/8)
    (he : ‖β-model a σ ψ δ‖≤C*(δ^3+η)) :
    (min 1 b/8)*(a+δ^2)≤‖β‖ :=
  positive_model_lower ha hδ hψ hb hnd hsmallσ he
    (absorb_spectral_remainder ha hδ hη hc hμ hidentity hC hb hsmallδ)

/-- This is the cusp inverse step after Poisson gives δ≥c q^(1/3).
No local inverse estimate or Dyson stability conclusion is assumed. -/
theorem inverse_from_beta_lower {β : ℂ} {δ A b c q p : ℝ}
    (hβ : b*δ^2≤‖β‖) (hb : 0<b) (hc : 0<c) (hq : 0<q)
    (hδ : c*q^p≤δ) :
    ‖β‖⁻¹≤(b*c^2)⁻¹*(q^p)⁻¹^2 := by
  have hp : 0<q^p := Real.rpow_pos_of_pos hq _
  have hd : 0<δ := (mul_pos hc hp).trans_le hδ
  have hlo : b*(c*q^p)^2≤‖β‖ :=
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ (by positivity) hd.le |>.mpr hδ) hb.le).trans hβ
  have hpos : 0<b*(c*q^p)^2 := by positivity
  have hinv := (inv_le_inv₀ (hpos.trans_le hlo) hpos).mpr hlo
  calc
    ‖β‖⁻¹≤(b*(c*q^p)^2)⁻¹ := hinv
    _=(b*c^2)⁻¹*(q^p)⁻¹^2 := by simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]

end NonSymmetricDyson.Paper.LinearBeta
