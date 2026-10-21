import Dyson.Paper.PerronDecomposition
import Dyson.Paper.PerronDoeblin

/-! The periodic Fourier gap from the original Markov proof. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Finset
namespace NonSymmetricDyson.Paper.Perron
variable {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]

theorem weightedInner_self_re (π : ι → ℝ) (x : ι → ℂ) :
    (weightedInner π x x).re=weightedSquare π x := by
  simp only [weightedInner, weightedSquare, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem periodVector_parseval_square (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (a : ZMod p → ℂ) :
    weightedSquare π (∑ k, a k • periodVector cls k)=∑ k, ‖a k‖^2 := by
  have h := congrArg Complex.re (periodVector_parseval π cls hmass a)
  rw [weightedInner_self_re] at h
  rw [h]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]

theorem unit_re_lt_one {z : ℂ} (hz : ‖z‖=1) (hne : z≠1) : z.re<1 := by
  have hle : z.re≤1 := by simpa [hz] using z.re_le_norm
  by_contra h
  have hr : z.re=1 := le_antisymm hle (le_of_not_gt h)
  have hn := Complex.sq_norm z
  rw [hz, Complex.normSq_apply, hr] at hn
  have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
  exact hne (Complex.ext (by simpa using hr) (by simpa using hi))

/-- A positive gap uniform in the full compact interval 0≤lam≤1. This also
handles period one, whose nonconstant periodic subspace is zero. -/
theorem exists_cyclic_gap (p : ℕ) [NeZero p] :
    ∃ c > 0, c≤1 ∧ ∀ k : ZMod p, k≠0 → ∀ lam : ℝ, 0≤lam → lam≤1 →
      c≤‖1-(lam:ℂ)*ZMod.stdAddChar (-k)‖ := by
  classical
  let g : ZMod p → ℝ := fun k => if k=0 then 1 else 1-(ZMod.stdAddChar (-k)).re
  have hg (k : ZMod p) : 0<g k := by
    by_cases hk : k=0
    · simp [g, hk]
    · have hne : ZMod.stdAddChar (-k)≠(1:ℂ) := by
        intro he
        have hz : ZMod.stdAddChar (-k)=ZMod.stdAddChar (0:ZMod p) := by simpa using he
        exact hk (neg_eq_zero.mp (ZMod.injective_stdAddChar hz))
      have hr := unit_re_lt_one ((ZMod.stdAddChar (N:=p)).norm_apply (-k)) hne
      simpa [g, hk] using sub_pos.mpr hr
  let vals := Finset.univ.image g
  have hvals : vals.Nonempty := by simp [vals]
  let c := min 1 (vals.min' hvals)
  have hc : 0<c := lt_min zero_lt_one (by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.min'_mem vals hvals)
    simpa [hk] using hg k)
  have hc1 : c≤1 := min_le_left _ _
  have hcg (k : ZMod p) : c≤g k := (min_le_right _ _).trans
    (Finset.min'_le vals (g k) (Finset.mem_image.mpr ⟨k,Finset.mem_univ k,rfl⟩))
  refine ⟨c,hc,hc1,?_⟩
  intro k hk lam hlam hlam1
  have hgk : c≤1-(ZMod.stdAddChar (-k)).re := by simpa [g,hk] using hcg k
  have hr : c≤(1-(lam:ℂ)*ZMod.stdAddChar (-k)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) (sub_nonneg.mpr hc1),
      mul_nonneg hlam (sub_nonneg.mpr hgk)]
  exact hr.trans (Complex.re_le_norm _)

theorem periodic_residual_expansion (Q : Matrix ι ι ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0≤Q i j) (hrow : ∀ i, ∑ j,Q i j=1)
    (hsupport : ∀ i j, 0<Q i j → cls j=cls i+1) (a : ZMod p → ℂ) (lam : ℝ) :
    (∑ k,a k • periodVector cls k) - (lam:ℂ) • Model.action Q (∑ k,a k • periodVector cls k) =
      ∑ k, ((1-(lam:ℂ)*ZMod.stdAddChar (-k))*a k) • periodVector cls k := by
  rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, periodVector_eigen Q cls hQ hrow hsupport]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Original Step 2: the weighted periodic gap follows from actual Fourier
orthogonality, the nontrivial character gap, and the vanishing constant mode. -/
theorem periodic_gap (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0≤Q i j) (hπ : ∀ i, 0≤π i) (hrow : ∀ i, ∑ j,Q i j=1)
    (hsupport : ∀ i j, 0<Q i j → cls j=cls i+1)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹)
    (c : ℝ) (hc : 0<c)
    (hgap : ∀ k : ZMod p,k≠0 → ∀ lam : ℝ,0≤lam → lam≤1 →
      c≤‖1-(lam:ℂ)*ZMod.stdAddChar (-k)‖)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1) (u : ι → ℂ)
    (hu : ClassConstant cls u) (hmean : ∑ i,(π i:ℂ)*u i=0) :
    c*weightedNorm π u≤weightedNorm π (u-(lam:ℂ) • Model.action Q u) := by
  obtain ⟨a,rfl⟩ := classConstant_fourier_expansion cls u hu
  have ha0 : a 0=0 := by rwa [mean_fourier_coefficients π cls hmass] at hmean
  have hsquare : c^2*weightedSquare π (∑ k,a k • periodVector cls k) ≤
      weightedSquare π ((∑ k,a k • periodVector cls k) -
        (lam:ℂ) • Model.action Q (∑ k,a k • periodVector cls k)) := by
    rw [periodic_residual_expansion Q cls hQ hrow hsupport,
      periodVector_parseval_square π cls hmass, periodVector_parseval_square π cls hmass,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k=0
    · simp [hk,ha0]
    · rw [norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖a k‖)
      have hb := hgap k hk lam hlam hlam1
      nlinarith [norm_nonneg (1-(lam:ℂ)*ZMod.stdAddChar (-k))]
  rw [← weightedNorm_sq π hπ, ← weightedNorm_sq π hπ] at hsquare
  nlinarith [weightedNorm_nonneg π (∑ k,a k • periodVector cls k),
    weightedNorm_nonneg π ((∑ k,a k • periodVector cls k)-
      (lam:ℂ) • Model.action Q (∑ k,a k • periodVector cls k))]

end NonSymmetricDyson.Paper.Perron
