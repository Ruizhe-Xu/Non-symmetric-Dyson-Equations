import Dyson.Paper.CyclicModes

/-! The appendix's reciprocal expansion and relative displacement calculation,
with an exact remainder and quantitative absorption. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full.CyclicGeneral Full.CyclicExample

/-- Literal reciprocal Taylor formula, valid without an asymptotic symbol. -/
theorem reciprocal_remainder (δ : ℂ) (hδ : 1+δ≠0) :
    (1+δ)⁻¹=1-δ+δ^2/(1+δ) := by field_simp; ring

theorem relative_equation (ζ : ℂ) (hζ : ‖ζ‖=1) (η : ℝ)
    (hm : scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)≠0) :
    let δ := scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)/ζ-1
    (ζ-ζ⁻¹)*δ+(η:ℂ)*Complex.I= -ζ⁻¹*δ^2/(1+δ) := by
  have hn : ζ≠0 := by intro he; simpa [he] using hζ
  let v := scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)
  have hmv : v≠0 := hm
  have hq : v^2+Full.CyclicGeneral.heightPoint (-2*ζ.re) η*v+1=0 := scalar_quadratic _
  have he : (2*ζ.re:ℂ)=ζ+ζ⁻¹ := by
    rw [Complex.inv_eq_conj hζ]
    apply Complex.ext <;> simp <;> ring
  have hz : Full.CyclicGeneral.heightPoint (-2*ζ.re) η= -(ζ+ζ⁻¹)+(η:ℂ)*Complex.I := by
    simp only [Full.CyclicGeneral.heightPoint,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
    rw [←he]
    push_cast
    ring
  change (ζ-ζ⁻¹)*(v/ζ-1)+(η:ℂ)*Complex.I= -ζ⁻¹*(v/ζ-1)^2/(1+(v/ζ-1))
  have hden : 1+(v/ζ-1)≠0 := by simpa using div_ne_zero hmv hn
  apply (mul_left_cancel₀ (mul_ne_zero hn hmv))
  field_simp [hden,hn,hmv]
  rw [hz] at hq
  field_simp [hn] at hq
  linear_combination ζ*hq

/-- The exact reciprocal remainder is O(δ²), with the manuscript coefficient
ζ−ζ⁻¹=2i Imζ made explicit. -/
theorem relative_linear_error (ζ δ : ℂ) (hζ : ‖ζ‖=1) (η : ℝ)
    (he : (ζ-ζ⁻¹)*δ+(η:ℂ)*Complex.I= -ζ⁻¹*δ^2/(1+δ))
    (hδ : ‖δ‖≤1/2) :
    ‖((2*ζ.im:ℂ)*Complex.I)*δ+(η:ℂ)*Complex.I‖≤2*‖δ‖^2 := by
  have hc : ζ-ζ⁻¹=(2*ζ.im:ℂ)*Complex.I := by
    rw [Complex.inv_eq_conj hζ]
    apply Complex.ext <;> simp <;> ring
  have hden : (1:ℝ)/2≤‖1+δ‖ := by
    have hh := norm_sub_le (1+δ) δ
    simp only [add_sub_cancel_right,norm_one] at hh
    linarith
  rw [←hc,he,norm_div,norm_mul,norm_neg,norm_inv,hζ,inv_one,one_mul,norm_pow]
  have hb := div_le_div_of_nonneg_left (sq_nonneg ‖δ‖) (by norm_num : (0:ℝ)<1/2) hden
  simpa [mul_comm] using hb

/-- Absorbing the δ² error first proves δ=O(η), and substituting back
produces the exact quadratic remainder claimed in the article. -/
theorem relative_taylor_of_small (ζ δ : ℂ) (η : ℝ) (hi : 0<ζ.im) (hη : 0≤η)
    (hδ : ‖δ‖≤ζ.im/2)
    (he : ‖((2*ζ.im:ℂ)*Complex.I)*δ+(η:ℂ)*Complex.I‖≤2*‖δ‖^2) :
    ‖δ+(η:ℂ)/(2*ζ.im:ℂ)‖≤(ζ.im)⁻¹^3*η^2 := by
  have hc : ‖(2*ζ.im:ℂ)*Complex.I‖=2*ζ.im := by
    simp [norm_mul,Complex.norm_real,abs_of_pos hi]
  have hsmall : ‖δ‖≤η/ζ.im := by
    have hh := norm_sub_le (((2*ζ.im:ℂ)*Complex.I)*δ+(η:ℂ)*Complex.I) ((η:ℂ)*Complex.I)
    simp only [add_sub_cancel_right,norm_mul,hc,Complex.norm_I,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hη] at hh
    have hquad := mul_le_mul_of_nonneg_left hδ (norm_nonneg δ)
    apply (le_div_iff₀ hi).mpr
    nlinarith
  have hid : ((2*ζ.im:ℂ)*Complex.I)*(δ+(η:ℂ)/(2*ζ.im:ℂ))=
      ((2*ζ.im:ℂ)*Complex.I)*δ+(η:ℂ)*Complex.I := by
    have him : (ζ.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hi.ne'
    field_simp
    <;> ring
  have hmul : 2*ζ.im*‖δ+(η:ℂ)/(2*ζ.im:ℂ)‖≤2*‖δ‖^2 := by
    simpa only [←hid,norm_mul,hc] using he
  have hs := (sq_le_sq₀ (norm_nonneg δ) (div_nonneg hη hi.le)).mpr hsmall
  have herr : ‖δ+(η:ℂ)/(2*ζ.im:ℂ)‖≤(η/ζ.im)^2/ζ.im := by
    apply (le_div_iff₀ hi).mpr
    nlinarith
  convert herr using 1 <;> field_simp <;> ring

/-- The literal appendix Taylor estimate, now obtained by the reciprocal
expansion and absorption, using continuity only to select the neighborhood. -/
theorem relative_taylor_algebraic (ζ : ℂ) (hζ : ‖ζ‖=1) (hi : 0<ζ.im) :
    ∃ C r : ℝ,0<C ∧ 0<r ∧ ∀η : ℝ,0<η → η<r →
      ‖scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)/ζ-1+(η:ℂ)/(2*ζ.im:ℂ)‖≤C*η^2 := by
  have hn : ζ≠0 := by intro he; simpa [he] using hζ
  have hlim : Tendsto (fun η:ℝ => scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)/ζ-1)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := (scalar_hasDerivAt_unit_energy ζ hζ hi).continuousAt.tendsto.comp
      (Full.CyclicGeneral.heightPoint_tendsto (-2*ζ.re))
    rw [scalar_at_unit_energy ζ hζ hi] at hh
    simpa [hn] using (hh.div_const ζ).sub_const 1
  have hnormlim : Tendsto (fun η:ℝ => ‖scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)/ζ-1‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hlim.norm
  have hsmall := hnormlim.eventually_lt_const (show (0:ℝ) < min (1/2) (ζ.im/2) by positivity)
  obtain ⟨r,hr,hrange⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  refine ⟨ζ.im⁻¹^3,r,by positivity,hr,?_⟩
  intro η hη hηr
  have hδ := hrange ⟨by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hη] using hηr,hη⟩
  have hmn : scalar (Full.CyclicGeneral.heightPoint (-2*ζ.re) η)≠0 := by
    intro he
    have hp := Full.CyclicGeneral.scalar_upper (show 0<(Full.CyclicGeneral.heightPoint (-2*ζ.re) η).im by simpa using hη)
    rw [he] at hp
    simpa using hp
  exact relative_taylor_of_small ζ _ η hi hη.le (hδ.le.trans (min_le_right _ _))
    (relative_linear_error ζ _ hζ η (relative_equation ζ hζ η hmn) (hδ.le.trans (min_le_left _ _)))

end NonSymmetricDyson.Paper.CyclicFourier
