import Dyson.Paper.LinearEdgeBeta

noncomputable section
namespace NonSymmetricDyson.Paper.LinearEdgeScale

/-- On the support side δ≈t and η≤t² imply a+δ≈t, with
a=μη/δ. This is the support-side comparison in the article. -/
theorem support_scale {a δ μ η t c C M : ℝ}
    (ha : 0≤a) (ht : 0<t) (hc : 0<c) (hη : 0≤η) (hηt : η≤t^2)
    (hμ : μ≤M) (hM : 0≤M) (hid : a*δ=μ*η)
    (hlo : c*t≤δ) (hhi : δ≤C*t) :
    c*t≤a+δ ∧ a+δ≤(M/c+C)*t := by
  have hp := mul_le_mul_of_nonneg_left hlo ha
  have hm := mul_le_mul_of_nonneg_right hμ hη
  have hηm := mul_le_mul_of_nonneg_left hηt hM
  have hprod : a*(c*t)≤M*t^2 := by nlinarith
  have hab : a≤(M/c)*t := by
    have hh := (le_div_iff₀ (mul_pos hc ht)).mpr hprod
    convert hh using 1 <;> field_simp <;> ring
  constructor <;> nlinarith

/-- On the gap side δ≈η/t; the positive real term a=μη/δ
is of size t. The η factor is cancelled only under η>0. -/
theorem gap_scale {a δ μ η t c C m M : ℝ}
    (ha : 0≤a) (ht : 0<t) (hc : 0<c) (hC : 0<C) (hm : 0< m)
    (hη : 0<η) (hηt : η≤t^2) (hμlo : m≤μ) (hμhi : μ≤M)
    (hid : a*δ=μ*η) (hlo : c*η≤δ*t) (hhi : δ*t≤C*η) :
    (m/C)*t≤a+δ ∧ a+δ≤(M/c+C)*t := by
  have hδ : 0<δ := by nlinarith
  have hloμ := mul_le_mul_of_nonneg_right hμlo hη.le
  have hhiμ := mul_le_mul_of_nonneg_right hμhi hη.le
  have haC := mul_le_mul_of_nonneg_left hhi ha
  have hac := mul_le_mul_of_nonneg_left hlo ha
  have hmul : a*δ*t=μ*η*t := by rw [hid]
  have hal : (m/C)*t≤a := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    have hprod : m*t*η≤a*C*η := by nlinarith [mul_le_mul_of_nonneg_right hloμ ht.le]
    have hh := (mul_le_mul_right hη).mp hprod
    exact hh
  have hau : a≤(M/c)*t := by
    have hprod : a*c*η≤M*t*η := by nlinarith [mul_le_mul_of_nonneg_right hhiμ ht.le]
    have hh := (mul_le_mul_right hη).mp hprod
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hc).mpr hh
  have hdu : δ≤C*t := by
    have hprod := mul_le_mul_of_nonneg_left hηt hC.le
    nlinarith
  constructor <;> nlinarith

theorem inverse_scale {N a δ t c C lo hi : ℝ}
    (ht : 0<t) (hc : 0<c) (hC : 0<C) (hlo : 0≤lo) (hhi : 0≤hi)
    (hscale : c*t≤a+δ ∧ a+δ≤C*t)
    (hinv : lo/(a+δ)≤N ∧ N≤hi/(a+δ)) :
    (lo/C)/t≤N ∧ N≤(hi/c)/t := by
  have hp : 0<a+δ := (mul_pos hc ht).trans_le hscale.1
  constructor
  · calc
      (lo/C)/t=lo/(C*t) := by ring
      _ ≤ lo/(a+δ) := div_le_div_of_nonneg_left hlo hp hscale.2
      _ ≤ N := hinv.1
  · calc
      N≤hi/(a+δ) := hinv.2
      _ ≤ hi/(c*t) := div_le_div_of_nonneg_left hhi (mul_pos hc ht) hscale.1
      _ = (hi/c)/t := by ring

end NonSymmetricDyson.Paper.LinearEdgeScale
