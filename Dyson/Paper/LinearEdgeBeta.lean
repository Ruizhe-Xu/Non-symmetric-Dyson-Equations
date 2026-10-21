import Dyson.Paper.LinearBeta

noncomputable section
namespace NonSymmetricDyson.Paper.LinearBeta

def edgeLeading (a σ δ : ℝ) : ℂ := (a:ℂ)-2*Complex.I*(σ:ℂ)*(δ:ℂ)

theorem edge_leading_lower {a σ δ s : ℝ} (ha : 0≤a) (hδ : 0≤δ)
    (hs : 0<s) (hσ : s≤|σ|) :
    (min 1 (2*s)/2)*(a+δ)≤‖edgeLeading a σ δ‖ := by
  have hr := Complex.abs_re_le_norm (edgeLeading a σ δ)
  have hi := Complex.abs_im_le_norm (edgeLeading a σ δ)
  have hra : a≤‖edgeLeading a σ δ‖ := by simpa [edgeLeading,abs_of_nonneg ha] using hr
  have hia : 2*s*δ≤‖edgeLeading a σ δ‖ := by
    have he : |(edgeLeading a σ δ).im|=2*|σ| * δ := by
      simp [edgeLeading,abs_mul,abs_of_nonneg hδ]
    rw [he] at hi
    exact (by nlinarith : 2*s*δ≤2*|σ| * δ).trans hi
  have h1 := mul_le_mul_of_nonneg_right (min_le_left 1 (2*s)) ha
  have h2 := mul_le_mul_of_nonneg_right (min_le_right 1 (2*s)) hδ
  nlinarith

theorem edge_beta_lower {β : ℂ} {a σ δ s : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hs : 0<s) (hσ : s≤|σ|)
    (he : ‖β-edgeLeading a σ δ‖≤(min 1 (2*s)/4)*(a+δ)) :
    (min 1 (2*s)/4)*(a+δ)≤‖β‖ := by
  have hm := edge_leading_lower ha hδ hs hσ
  have ht : ‖edgeLeading a σ δ‖≤‖β-edgeLeading a σ δ‖+‖β‖ := by
    simpa [dist_eq_norm,norm_sub_rev] using dist_triangle (edgeLeading a σ δ) β 0
  nlinarith

theorem edge_beta_upper {β : ℂ} {a σ δ M R : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hM : 0≤M) (hσ : |σ|≤M)
    (he : ‖β-edgeLeading a σ δ‖≤R*(a+δ)) :
    ‖β‖≤(1+2*M+R)*(a+δ) := by
  have hm : ‖edgeLeading a σ δ‖≤a+2*M*δ := by
    calc
      _ ≤ ‖(a:ℂ)‖+‖2*Complex.I*(σ:ℂ)*(δ:ℂ)‖ := norm_sub_le _ _
      _ = a+2*|σ| * δ := by
        simp [norm_mul,Complex.norm_real,abs_of_nonneg ha,abs_of_nonneg hδ]
      _ ≤ a+2*M*δ := by nlinarith
  have ht : ‖β‖≤‖β-edgeLeading a σ δ‖+‖edgeLeading a σ δ‖ := by
    simpa [dist_eq_norm] using dist_triangle β (edgeLeading a σ δ) 0
  nlinarith [mul_nonneg hM ha]

/-- Original edge second-order and Taylor errors are small relative to
a+δ; this handles support and gap sides in a single algebraic statement. -/
theorem edge_remainder_absorption {β : ℂ} {a σ ψ δ η μ c C D ε : ℝ}
    (ha : 0≤a) (hδ : 0≤δ) (hδ1 : δ≤1) (hη : 0≤η)
    (hc : 0<c) (hμ : c≤μ) (hidentity : μ*η=a*δ)
    (hC : 0≤C) (hD : 0≤D) (hquad : |ψ-σ^2|≤D)
    (hsmall : (2*D+C*(1+c⁻¹))*δ≤ε)
    (he : ‖β-model a σ ψ δ‖≤C*(δ^3+η)) :
    ‖β-edgeLeading a σ δ‖≤ε*(a+δ) := by
  have heta : η≤a*δ/c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hquadnorm : ‖model a σ ψ δ-edgeLeading a σ δ‖≤2*D*δ^2 := by
    have hid : model a σ ψ δ-edgeLeading a σ δ=
      2*((ψ-σ^2:ℝ):ℂ)*(δ:ℂ)^2 := by unfold model edgeLeading; ring
    rw [hid,norm_mul,norm_mul,norm_pow]
    simp only [Complex.norm_real,Real.norm_eq_abs]
    norm_num
    nlinarith [sq_abs δ,mul_le_mul_of_nonneg_right hquad (sq_nonneg δ)]
  have ht : ‖β-edgeLeading a σ δ‖≤‖β-model a σ ψ δ‖+‖model a σ ψ δ-edgeLeading a σ δ‖ := by
    simpa [dist_eq_norm] using dist_triangle β (model a σ ψ δ) (edgeLeading a σ δ)
  have hnonneg : 0≤C*c⁻¹*δ := mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hc.le)) hδ
  have hprod := mul_le_mul_of_nonneg_left hδ1 (show 0≤C*δ^2 by positivity)
  have h1 := mul_le_mul_of_nonneg_right hsmall hδ
  have h2 := mul_le_mul_of_nonneg_right hsmall ha
  have h3 := mul_le_mul_of_nonneg_left heta hC
  have haD : 0≤(2*D+C)*δ*a := by positivity
  simp only [div_eq_mul_inv] at h3
  nlinarith

end NonSymmetricDyson.Paper.LinearBeta
