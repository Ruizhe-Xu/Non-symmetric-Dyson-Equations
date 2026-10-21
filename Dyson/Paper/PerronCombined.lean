import Dyson.Paper.PerronCyclicGap
import Dyson.Paper.PerronMixing

/-! Original Step 4: combine the orthogonal periodic and mixing estimates.
The resulting bound actually invokes both the Fourier and Doeblin proofs. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace NonSymmetricDyson.Paper.Perron
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [NeZero p]

theorem weightedSquare_add (π : ι → ℝ) (u v : ι → ℂ) :
    weightedSquare π (u+v)=weightedSquare π u+weightedSquare π v+
      2*(weightedInner π u v).re := by
  have hpoint (i : ι) : π i*‖(u+v) i‖^2=
      π i*‖u i‖^2+π i*‖v i‖^2+2*((π i:ℂ)*conj (u i)*v i).re := by
    simp only [Pi.add_apply,Complex.sq_norm,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
    ring
  simp only [weightedSquare,hpoint,Finset.sum_add_distrib,weightedInner,
    Complex.re_sum,Finset.mul_sum]

theorem weightedNorm_pythagoras (π : ι → ℝ) (hπ : ∀ i,0≤π i)
    (u v : ι → ℂ) (horth : weightedInner π u v=0) :
    weightedNorm π (u+v)^2=weightedNorm π u^2+weightedNorm π v^2 := by
  simp_rw [weightedNorm_sq π hπ]
  rw [weightedSquare_add,horth]
  simp

theorem classMean_smul (π : ι → ℝ) (cls : ι → ZMod p) (c : ZMod p)
    (a : ℂ) (x : ι → ℂ) : classMean π cls c (a • x)=a*classMean π cls c x := by
  simp only [classMean,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem classConstant_action (Q : Matrix ι ι ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j,0≤Q i j) (hrow : ∀ i,∑ j,Q i j=1)
    (hsupport : ∀ i j,0<Q i j → cls j=cls i+1)
    (a : ZMod p → ℂ) : Model.action Q (fun i => a (cls i))=fun i => a (cls i+1) := by
  ext i
  change (∑ j,(Q i j:ℂ)*a (cls j))=_
  calc
    _ = ∑ j,(Q i j:ℂ)*a (cls i+1) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hq : Q i j=0
      · simp [hq]
      · rw [hsupport i j (lt_of_le_of_ne (hQ i j) (Ne.symm hq))]
    _ = _ := by rw [← Finset.sum_mul,← Complex.ofReal_sum,hrow i]; simp

theorem classConstant_residual (Q : Matrix ι ι ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j,0≤Q i j) (hrow : ∀ i,∑ j,Q i j=1)
    (hsupport : ∀ i j,0<Q i j → cls j=cls i+1)
    (lam : ℝ) (u : ι → ℂ) (hu : ClassConstant cls u) :
    ClassConstant cls (u-(lam:ℂ) • Model.action Q u) := by
  obtain ⟨a,ha⟩ := hu
  have he : u=fun i => a (cls i) := funext ha
  rw [he,classConstant_action Q cls hQ hrow hsupport]
  exact ⟨fun c => a c-(lam:ℂ)*a (c+1),fun _ => rfl⟩

theorem classCentered_residual (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j,0≤Q i j) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (hsupport : ∀ i j,0<Q i j → cls j=cls i+1)
    (lam : ℝ) (v : ι → ℂ) (hv : ClassCentered π cls v) :
    ClassCentered π cls (v-(lam:ℂ) • Model.action Q v) := by
  intro c
  rw [classMean_sub,classMean_smul,classMean_action Q π cls hQ hstat hsupport,
    hv c,hv (c+1),mul_zero,sub_self]

/-- The original orthogonal-combination argument, with a single explicit
constant c*θ/(L+1) valid even when the period is one. -/
theorem original_weighted_gap
    (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j,0≤Q i j) (hπ : ∀ i,0≤π i)
    (hrow : ∀ i,∑ j,Q i j=1) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (hsupport : ∀ i j,0<Q i j → cls j=cls i+1)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹)
    (L : ℕ) (hL : 0<L) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
    (hpower : ∀ i j,cls i=cls j → θ≤(Q^L) i j)
    (c : ℝ) (hc : 0<c) (hc1 : c≤1)
    (hgap : ∀ k : ZMod p,k≠0 → ∀ lam : ℝ,0≤lam → lam≤1 →
      c≤‖1-(lam:ℂ)*ZMod.stdAddChar (-k)‖)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (x : ι → ℂ) (hx : ∑ i,(π i:ℂ)*x i=0) :
    (c*θ/((L:ℝ)+1))*weightedNorm π x≤weightedNorm π (x-(lam:ℂ) • Model.action Q x) := by
  obtain ⟨u,v,rfl,hu,hv,hov,hmean⟩ := periodic_mixing_decomposition π cls hmass x
  have hmean0 : ∑ i,(π i:ℂ)*u i=0 := hmean.trans hx
  have hper := periodic_gap Q π cls hQ hπ hrow hsupport hmass c hc hgap lam hlam hlam1 u hu hmean0
  have hmix := class_centered_gap Q π cls hQ hπ hrow hstat hmass L hL θ hθ.le hθ1 hpower
    lam hlam hlam1 v hv
  let g : ℝ := c*θ/((L:ℝ)+1)
  have hLr : 0<(L:ℝ) := by exact_mod_cast hL
  have hg : 0≤g := by dsimp [g]; positivity
  have hgc : g≤c := (div_le_iff₀ (by positivity : 0<(L:ℝ)+1)).mpr (by nlinarith)
  have hgm : g≤θ/(L:ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0<(L:ℝ)+1) hLr).mpr
    nlinarith [mul_nonneg hLr.le (sub_nonneg.mpr hc1)]
  have hru := (mul_le_mul_of_nonneg_right hgc (weightedNorm_nonneg π u)).trans hper
  have hrv := (mul_le_mul_of_nonneg_right hgm (weightedNorm_nonneg π v)).trans hmix
  have hrs : weightedInner π (u-(lam:ℂ) • Model.action Q u)
      (v-(lam:ℂ) • Model.action Q v)=0 := classCentered_orthogonal π cls _ _
    (classConstant_residual Q cls hQ hrow hsupport lam u hu)
    (classCentered_residual Q π cls hQ hstat hsupport lam v hv)
  have hsq := weightedNorm_pythagoras π hπ u v hov
  have hsqR := weightedNorm_pythagoras π hπ _ _ hrs
  have he : (u+v)-(lam:ℂ) • Model.action Q (u+v)=
      (u-(lam:ℂ) • Model.action Q u)+(v-(lam:ℂ) • Model.action Q v) := by
    rw [map_add,smul_add]
    abel
  rw [he]
  have hu2 : (g*weightedNorm π u)^2≤weightedNorm π (u-(lam:ℂ) • Model.action Q u)^2 :=
    (sq_le_sq₀ (mul_nonneg hg (weightedNorm_nonneg π u))
      (weightedNorm_nonneg π _)).mpr hru
  have hv2 : (g*weightedNorm π v)^2≤weightedNorm π (v-(lam:ℂ) • Model.action Q v)^2 :=
    (sq_le_sq₀ (mul_nonneg hg (weightedNorm_nonneg π v))
      (weightedNorm_nonneg π _)).mpr hrv
  change g*weightedNorm π (u+v)≤_
  apply (sq_le_sq₀ (mul_nonneg hg (weightedNorm_nonneg π _)) (weightedNorm_nonneg π _)).mp
  rw [mul_pow,hsq,hsqR,mul_add]
  nlinarith only [hu2,hv2]

end NonSymmetricDyson.Paper.Perron
