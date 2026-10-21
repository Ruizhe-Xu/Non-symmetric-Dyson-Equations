import Dyson.Paper.LinearSpectralTransfer
import Dyson.Full.PerronDensityActual

noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.LinearFrame
open Full Full.Singularities Full.SingularSpectral Full.Spectral Full.PerronContinuation
variable {X : Type*} {n : ℕ} [Nonempty (Fin n)]

theorem quadratic_tendsto (L : Filter X) (p : Fin n → ℝ)
    (l r : X → Fin n → ℝ) (l₀ r₀ : Fin n → ℝ)
    (hl : Tendsto l L (𝓝 l₀)) (hr : Tendsto r L (𝓝 r₀)) :
    Tendsto (fun x => quadraticCoefficient p (l x) (r x)) L
      (𝓝 (quadraticCoefficient p l₀ r₀)) := by
  unfold quadraticCoefficient
  exact tendsto_finset_sum _ (fun i _ =>
    (((continuous_apply i).continuousAt.tendsto.comp hl).mul_const (p i)).mul
      (((continuous_apply i).continuousAt.tendsto.comp hr).pow 2))

theorem mass_tendsto (L : Filter X) (l : X → Fin n → ℝ) (l₀ : Fin n → ℝ)
    (m : X → Fin n → ℂ) (m₀ : Fin n → ℂ)
    (hl : Tendsto l L (𝓝 l₀)) (hm : Tendsto m L (𝓝 m₀)) :
    Tendsto (fun x => ∑ i,l x i*‖m x i‖) L (𝓝 (∑ i,l₀ i*‖m₀ i‖)) :=
  tendsto_finset_sum _ (fun i _ =>
    ((continuous_apply i).continuousAt.tendsto.comp hl).mul
      (((continuous_apply i).continuousAt.tendsto.comp hm).norm))

/-- The δ⁻² bound is now obtained by the article's β expansion, positivity
and inverse spectral decomposition.  The only scalar hypothesis is the
separately proved σ²+ψ nondegeneracy, never an inverse estimate. -/
theorem inverse_from_frame
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n)) (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (L : Filter X) (z : X → ℂ) (m : X → Fin n → ℂ) (m₀ : Fin n → ℂ)
    (frame : VaryingFrame S m L m₀)
    (hm : Tendsto m L (𝓝 m₀)) (hη : Tendsto (fun x => (z x).im) L (𝓝 0))
    (hreal : ∀i,(m₀ i).im=0) (hnz : ∀i,m₀ i≠0)
    (p : Fin n → ℝ) (hp : ∀i,p i^2=1) (hp0 : ∀i,0<p i*(m₀ i).re)
    (hactual : ∀ᶠ x in L,0<(z x).im ∧ BasicEstimates.IsUpperSolution (m x) ∧
      BasicEstimates.IsDysonSolution S a (z x) (m x))
    (b : ℝ) (hb : 0<b)
    (hnd : ∀ᶠ x in L,b≤(quadraticCoefficient p (frame.l x) (frame.r x))^2+
      cubicCoefficient (saturatedMatrix S (m x)) p (frame.l x) (frame.r x)
        (stableCoefficient p (frame.r x) (frame.K x))) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ x in L,∀ (hz : 0<(z x).im)
      (hu : BasicEstimates.IsUpperSolution (m x))
      (heq : BasicEstimates.IsDysonSolution S a (z x) (m x)),
      ‖EuclideanInverse.stabilityInverse S a (z x) (m x) hS hz hu heq‖≤
        C/(perronDensity (frame.l x) (m x))^2 := by
  let δ := fun x => perronDensity (frame.l x) (m x)
  let σ := fun x => quadraticCoefficient p (frame.l x) (frame.r x)
  let μ := fun x => ∑i,frame.l x i*‖m x i‖
  let μ₀ := ∑i,frame.l₀ i*‖m₀ i‖
  have hμ₀ : 0<μ₀ := Finset.sum_pos (fun i _ =>
    mul_pos (frame.center.left_positive i) (norm_pos_iff.mpr (hnz i))) Finset.univ_nonempty
  have hμlim : Tendsto μ L (𝓝 μ₀) := mass_tendsto L frame.l frame.l₀ m m₀ frame.left_limit hm
  have hμlo := hμlim.eventually_const_le (show μ₀/2<μ₀ by linarith)
  have hδlim : Tendsto δ L (𝓝 0) :=
    perronDensity_tendsto_zero L m m₀ frame.l frame.l₀ hm frame.left_limit hreal hnz
  have hσlim : Tendsto σ L (𝓝 (quadraticCoefficient p frame.l₀ frame.r₀)) :=
    quadratic_tendsto L p frame.l frame.r _ _ frame.left_limit frame.right_limit
  have hσδlim : Tendsto (fun x => |σ x| * δ x) L (𝓝 0) := by
    simpa using hσlim.abs.mul hδlim
  have hσsmall := hσδlim.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hactual' : ∀ᶠ x in L,(∀i,m x i≠0) ∧ BasicEstimates.IsDysonSolution S a (z x) (m x) ∧
      (∀i,0≤normalizedImag (m x) i) ∧ 0≤(z x).im := by
    filter_upwards [hactual] with x hx
    exact ⟨fun i => BasicEstimates.component_ne_zero hx.2.1 i,hx.2.2,
      fun i => div_nonneg (hx.2.1 i).le (norm_nonneg _),hx.1.le⟩
  obtain ⟨ρ,C,hρ,hC,hspec⟩ := varying_spectral_expansion hn external S a L z m m₀ frame
    hm hη hreal hnz p hp hp0 hactual'
  have hsmalllim : Tendsto (fun x => C*(1+(μ₀/2)⁻¹)*δ x) L (𝓝 0) := by
    simpa using hδlim.const_mul (C*(1+(μ₀/2)⁻¹))
  have hsmall := hsmalllim.eventually_le_const (show (0:ℝ)< min 1 b/8 by positivity)
  obtain ⟨q,hq,hqlow⟩ := positive_component_lower_bound m _ hm hnz
  let Q := ‖m₀‖+1
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hQbound := hm.norm.eventually_le_const (show ‖m₀‖<Q by dsimp [Q]; linarith)
  let B := Real.sqrt (Fintype.card (Fin n))*C*(1+ρ/2)
  let A := (Real.sqrt (Fintype.card (Fin n)))^2*(Q/q)
  have hB : 0<B := by dsimp [B]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A*B/(min 1 b/8),by positivity,?_⟩
  filter_upwards [hspec,hμlo,hσsmall,hsmall,hnd,frame.nearby,frame.restricted,hqlow,hQbound]
    with x hx hμx hσx hsmallx hndx hframe hK hqlo hQhi
  intro hz hu heq
  obtain ⟨u,d,hKu,hd⟩ := hx
  have hueq := stableCoefficient_eq_of_quadratic_image p (frame.r x) u (frame.K x) hKu
  rw [← hueq] at hd
  have hψ := actual_cubic_positive_upper S a (z x) (m x) hS hz hu heq
    p (frame.r x) (frame.l x) (frame.lam x) hframe (frame.K x) hK
  obtain ⟨hδ,hlam⟩ := perron_eigenvalue_identity S a (z x) (m x) hu heq
    (frame.l x) (frame.lam x) hframe.left_positive hframe.left_eigen
  change 0<δ x at hδ
  have hid : μ x*(z x).im=(1-frame.lam x)*δ x := by
    change frame.lam x=1-(z x).im*μ x/δ x at hlam
    rw [hlam]
    field_simp
    ring
  have ha : 0≤1-frame.lam x := (sub_pos.mpr
    (perron_eigenvalue_lt_one S a (z x) (m x) hz hu heq (frame.l x)
      (frame.lam x) hframe.left_positive hframe.left_eigen)).le
  have hlower := LinearBeta.beta_lower_from_original_expansion ha hδ.le hz.le hψ
    (half_pos hμ₀) hμx hid hC.le hb hndx hσx hsmallx
      (LinearSpectralTransfer.beta_remainder hd)
  have hdensity : (min 1 b/8)*(δ x)^2≤‖d.value‖ := by
    nlinarith [mul_nonneg (show 0≤ min 1 b/8 by positivity) ha]
  have hβ := spectral_value_ne_zero_upper S a (z x) (m x) hS hz hu heq d
  have hinv := (spectral_estimates_inverse_consequences hρ hC d hd).2 hβ
  have htrans := LinearSpectralTransfer.stability_inverse_norm_transfer S a (z x) (m x)
    hS hz hu heq q Q hq hQ hqlo (fun i => (norm_le_pi_norm (m x) i).trans hQhi) d
  have hninv : ‖d.value‖⁻¹≤((min 1 b/8)*(δ x)^2)⁻¹ :=
    (inv_le_inv₀ (norm_pos_iff.mpr hβ) (by positivity)).mpr hdensity
  have hh := htrans.trans (mul_le_mul_of_nonneg_left
    (hinv.2.2.2.trans (mul_le_mul_of_nonneg_left hninv hB.le)) hA.le)
  convert hh using 1 <;> dsimp [A,B,δ] <;> field_simp <;> ring

end NonSymmetricDyson.Paper.LinearFrame
