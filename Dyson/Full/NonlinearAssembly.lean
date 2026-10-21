import Dyson.Full.NonlinearReduction
import Dyson.Full.NonlinearRough

/-! Uniform local reduction data used to assemble the nonlinear theorem.
The package below is constructed from the actual normalized polynomial and
standard analytic theorems; none of its estimates is an external hypothesis. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

/-- Retain uniqueness when shrinking the stable elimination neighborhood to
obtain the quantitative quadratic size estimate. -/
theorem analytic_stable_elimination_full
    (ift : AnalyticImplicitFunctionPrinciple (ι → ℂ) (ℂ × (ι → ℂ)))
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ) :
    ∃ W : ℂ × (ι → ℂ) → (ι → ℂ), AnalyticAt ℂ W 0 ∧ W 0 = 0 ∧
      ∃ εw > 0, ∃ εp > 0, ∃ C > 0,
        (∀ v, ‖v‖ < εp → W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2)) ∧
        (∀ v, ‖v‖ < εp → ‖W v‖ ≤ C * (‖v.1‖^2 + ‖v.2‖)) ∧
        (∀ w v, ‖w‖ < εw → ‖v‖ < εp →
          (w = K (quadraticNonlinearity F p q (v.1 • r + w) v.2) ↔ w = W v)) := by
  obtain ⟨W, hWa, hW0, εw, hεw, εp, hεp, hW, huniq⟩ :=
    analytic_stable_elimination ift F K p q r
  have hcont : ContinuousAt (fun v : ℂ × (ι → ℂ) => ‖v.1 • r + W v‖) 0 :=
    ((continuousAt_fst.smul continuousAt_const).add hWa.continuousAt).norm
  have hcsmall : ContinuousAt (fun v : ℂ × (ι → ℂ) =>
      4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W v‖) 0 :=
    continuousAt_const.mul hWa.continuousAt.norm
  have hevent : ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 0,
      ‖v‖ < εp ∧ ‖v.1 • r + W v‖ < 1 ∧
        4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W v‖ < 1 := by
    have h₁ : ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 0, ‖v‖ < εp :=
      continuousAt_id.norm.eventually_lt continuousAt_const (by simpa using hεp)
    have h₂ := hcont.eventually_lt continuousAt_const
      (show ‖(0 : ℂ × (ι → ℂ)).1 • r + W 0‖ < 1 by simp [hW0])
    have h₃ := hcsmall.eventually_lt continuousAt_const
      (show 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖W 0‖ < 1 by simp [hW0])
    filter_upwards [h₁, h₂, h₃] with v h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let A := 4 * (‖K‖ * ‖p‖ * ‖F‖) * ‖r‖ ^ 2
  let B := 2 * ‖K‖ * ‖q‖ * (1 + ‖p‖)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨W, hWa, hW0, εw, hεw, ε, hε, 1+A+B, by positivity, ?_, ?_, ?_⟩
  · intro v hv
    exact (hW v (hball (by simpa using hv)).1).1
  · intro v hv
    have h := hball (by simpa using hv)
    have heq := (hW v h.1).1
    have hb : ‖W v‖ ≤ A * ‖v.1‖^2 + B * ‖v.2‖ :=
      stable_fixed_point_size F K p q r (W v) v.2 v.1 heq h.2.1.le h.2.2.le
    calc
      _ ≤ A * ‖v.1‖^2 + B * ‖v.2‖ := hb
      _ ≤ (1+A+B)*‖v.1‖^2 + (1+A+B)*‖v.2‖ := by gcongr <;> linarith
      _ = _ := by ring
  · intro w v hw hv
    exact huniq w v hw (hball (by simpa using hv)).1

/-- A proved local coordinate package. The constructor theorem below supplies
all fields from the generic analytic inputs and restricted inverse. -/
structure LocalReduction
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (k : ℕ) where
  W : ℂ × (ι → ℂ) → (ι → ℂ)
  W_analytic : AnalyticAt ℂ W 0
  W_zero : W 0 = 0
  radius : ℝ
  radius_pos : 0 < radius
  roughConstant : ℝ
  roughConstant_pos : 0 < roughConstant
  lipschitzConstant : ℝ
  lipschitzConstant_pos : 0 < lipschitzConstant
  residualConstant : ℝ
  residualConstant_pos : 0 < residualConstant
  rootRadius : ℝ
  rootRadius_pos : 0 < rootRadius
  separation : ℝ
  separation_pos : 0 < separation
  rootBound : ℝ
  rootBound_pos : 0 < rootBound
  roots : Fin k → ℂ → ℂ
  roots_continuous : ∀ j, ContinuousOn (roots j) {ω | 0 < ω.im ∧ ‖ω‖ < rootRadius}
  root_data : ∀ ω, 0 < ω.im → ‖ω‖ < rootRadius →
    (∀ j, spectralScalar F ℓ p q r W (roots j ω, ω) = 0 ∧
      separation * ‖ω‖ ^ ((1:ℝ)/k) ≤ ‖roots j ω‖ ∧
      ‖roots j ω‖ ≤ rootBound * ‖ω‖ ^ ((1:ℝ)/k)) ∧
    (∀ i j, i ≠ j → separation * ‖ω‖ ^ ((1:ℝ)/k) ≤ ‖roots i ω-roots j ω‖)
  product_bound : ∀ h ω, ‖h‖ < radius → 0 < ω.im → ‖ω‖ < rootRadius →
    separation * (∏ j, ‖ℓ h-roots j ω‖) ≤ ‖spectralScalar F ℓ p q r W (ℓ h,ω)‖
  reduce : ∀ h ξ, ‖h‖ < radius → ‖ξ‖ < radius →
    h-F h = quadraticNonlinearity F p q h ξ →
    h = ℓ h • r + W (ℓ h,ξ) ∧ reducedScalar F ℓ p q r W (ℓ h,ξ) = 0
  rough : ∀ h ξ, ‖h‖ < radius → ‖ξ‖ < radius →
    h-F h = quadraticNonlinearity F p q h ξ →
    ‖h‖ ≤ roughConstant * ‖ξ‖ ^ ((1:ℝ)/k)
  stable_lipschitz : ∀ h₁ h₂ ξ₁ ξ₂, ‖h₁‖ < radius → ‖h₂‖ < radius →
    ‖ξ₁‖ < radius → ‖ξ₂‖ < radius →
    ‖W (ℓ h₁,ξ₁)-W (ℓ h₂,ξ₂)‖ ≤
      lipschitzConstant * (‖ℓ h₁-ℓ h₂‖+‖ξ₁-ξ₂‖)
  scalar_residual : ∀ h ω R, ‖h‖ < radius → ‖ω • (1:ι→ℂ)‖ < radius →
    ‖ω • (1:ι→ℂ)+R‖ < radius →
    reducedScalar F ℓ p q r W (ℓ h,ω • (1:ι→ℂ)+R) = 0 →
    ‖spectralScalar F ℓ p q r W (ℓ h,ω)‖ ≤ residualConstant * ‖R‖

/-- Construction of one common local neighborhood for every part of the
nonlinear argument, before choosing an approximate solution or a path. -/
theorem localReduction_exists
    (ift : AnalyticImplicitFunctionPrinciple (ι → ℂ) (ℂ × (ι → ℂ)))
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hFr : F r = r) (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hK : Singularities.IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r)
    (k : ℕ) (γ : ℂ) (hγ : γ ≠ 0) (hμ : ℓ q ≠ 0)
    (hcase : (k=2 ∧ γ=ℓ (p*r*r)) ∨
      (k=3 ∧ ℓ (p*r*r)=0 ∧ γ=ℓ (p*r*(F (K (p*r*r))+K (p*r*r))))) :
    Nonempty (LocalReduction F K ℓ p q r k) := by
  obtain ⟨W,hWa,hW0,εw,hεw,εp,hεp,C,hC,hfixed,hsize,huniq⟩ :=
    analytic_stable_elimination_full ift F K p q r
  obtain ⟨ρ,hρ,δ,hδ,c,hc,Cr,hCr,roots,hroots,hroot⟩ :=
    actual_spectral_root_factorization rootArgument F K ℓ p q r hFr W hWa
      εp C hεp hC hfixed hsize k γ hγ hμ hcase
  obtain ⟨εL,hεL,L,hL,hLip⟩ := analytic_local_lipschitz W hWa
  obtain ⟨εS,hεS,CS,hCS,hres⟩ := scalar_forcing_residual_bound F ℓ p q r W hWa
  obtain ⟨εR,hεR,CR,hCR,hrough⟩ := actual_rough_vector_root_bound F K ℓ p q r hFr k γ hγ hcase
  let θ : (ι→ℂ) × (ι→ℂ) → ℂ := fun v => ℓ v.1
  let w : (ι→ℂ) × (ι→ℂ) → (ι→ℂ) := fun v => v.1 - ℓ v.1 • r
  let vpar : (ι→ℂ) × (ι→ℂ) → ℂ × (ι→ℂ) := fun v => (ℓ v.1,v.2)
  have hcθ : Continuous θ := ℓ.continuous.comp continuous_fst
  have hcw : Continuous w := continuous_fst.sub (hcθ.smul continuous_const)
  have hcp : Continuous vpar := hcθ.prodMk continuous_snd
  have hev : ∀ᶠ v : (ι→ℂ) × (ι→ℂ) in 𝓝 0,
      ‖v.1‖ < 1 ∧ 4*(‖K‖*‖p‖*‖F‖)*‖w v‖ < 1 ∧
      ‖θ v‖ < εR ∧ ‖v.2‖ < εR ∧ ‖w v‖ < εw ∧
      ‖vpar v‖ < εp ∧ ‖θ v‖ < ρ ∧ ‖vpar v‖ < εL ∧ ‖vpar v‖ < εS := by
    have a₁ := continuous_fst.norm.continuousAt.eventually_lt continuousAt_const
      (show ‖((0 : (ι→ℂ) × (ι→ℂ)).1)‖ < 1 by simp)
    have a₂ := (continuous_const.mul hcw.norm).continuousAt.eventually_lt continuousAt_const
      (show 4*(‖K‖*‖p‖*‖F‖)*‖w 0‖ < 1 by simp [w])
    have a₃ := (hcθ.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [θ] using hεR)
    have a₄ := continuous_snd.norm.continuousAt.eventually_lt continuousAt_const
      (show ‖((0 : (ι→ℂ) × (ι→ℂ)).2)‖ < εR by simpa using hεR)
    have a₅ := (hcw.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [w] using hεw)
    have a₆ := (hcp.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [vpar] using hεp)
    have a₇ := (hcθ.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [θ] using hρ)
    have a₈ := (hcp.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [vpar] using hεL)
    have a₉ := (hcp.norm.continuousAt (x := 0)).eventually_lt continuousAt_const (by simpa [vpar] using hεS)
    filter_upwards [a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉] with v a b c d e f g h i
    exact ⟨a,b,c,d,e,f,g,h,i⟩
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hctrl : ∀ (h ξ : ι → ℂ), ‖h‖ < ε → ‖ξ‖ < ε →
      ‖h‖ < 1 ∧ 4*(‖K‖*‖p‖*‖F‖)*‖h-ℓ h • r‖ < 1 ∧
      ‖ℓ h‖ < εR ∧ ‖ξ‖ < εR ∧ ‖h-ℓ h • r‖ < εw ∧
      ‖(ℓ h,ξ)‖ < εp ∧ ‖ℓ h‖ < ρ ∧ ‖(ℓ h,ξ)‖ < εL ∧ ‖(ℓ h,ξ)‖ < εS := by
    intro h ξ hh hξ
    simpa [θ,w,vpar] using hball (y := (h,ξ))
      (by simpa [dist_eq_norm, Prod.norm_def] using max_lt hh hξ)
  refine ⟨{
    W := W, W_analytic := hWa, W_zero := hW0,
    radius := ε, radius_pos := hε, roughConstant := CR, roughConstant_pos := hCR,
    lipschitzConstant := L, lipschitzConstant_pos := hL,
    residualConstant := CS, residualConstant_pos := hCS,
    rootRadius := δ, rootRadius_pos := hδ, separation := c, separation_pos := hc,
    rootBound := Cr, rootBound_pos := hCr, roots := roots, roots_continuous := hroots,
    root_data := fun ω hω hn => ⟨(hroot ω hω hn).1, (hroot ω hω hn).2.1⟩,
    product_bound := ?_, reduce := ?_, rough := ?_, stable_lipschitz := ?_, scalar_residual := ?_
  }⟩
  · intro h ω hh hω hn
    exact ((hroot ω hω hn).2.2 (ℓ h) (hctrl h 0 hh (by simpa using hε)).2.2.2.2.2.2.1.le).1
  · intro h ξ hh hξ he
    have ht := hctrl h ξ hh hξ
    exact (local_reduction_equivalence F K ℓ p q r h ξ hFr hlF hK W εw εp
      hfixed huniq ht.2.2.2.2.1 ht.2.2.2.2.2.1).mp he
  · intro h ξ hh hξ he
    have ht := hctrl h ξ hh hξ
    have hpj := (Singularities.projected_residual_iff F.toLinearMap K.toLinearMap ℓ.toLinearMap
      r h (quadraticNonlinearity F p q h ξ) hlF hK.kill_right hFr hK.left_inverse hK.right_inverse).mp he
    have hw : h-ℓ h • r = K (quadraticNonlinearity F p q (ℓ h • r+(h-ℓ h • r)) ξ) := by
      have hh : h = ℓ h • r + K (quadraticNonlinearity F p q h ξ) := hpj.1
      rw [show ℓ h • r+(h-ℓ h • r)=h by abel]
      calc
        _ = (ℓ h • r + K (quadraticNonlinearity F p q h ξ)) - ℓ h • r :=
          congrArg (fun u => u-ℓ h • r) hh
        _ = _ := by abel
    have hrec : ℓ h • r+(h-ℓ h • r)=h := by abel
    have hb := hrough (ℓ h) (h-ℓ h • r) ξ hw (by simpa [hrec] using ht.1.le)
      ht.2.1.le ht.2.2.1.le ht.2.2.2.1.le (by simpa only [hrec] using hpj.2)
    simpa only [hrec] using hb
  · intro h₁ h₂ ξ₁ ξ₂ hh₁ hh₂ hξ₁ hξ₂
    have ht₁ := hctrl h₁ ξ₁ hh₁ hξ₁
    have ht₂ := hctrl h₂ ξ₂ hh₂ hξ₂
    have h := hLip (ℓ h₁,ξ₁) (ℓ h₂,ξ₂) ht₁.2.2.2.2.2.2.2.1 ht₂.2.2.2.2.2.2.2.1
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hL.le
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using
      max_le_add_of_nonneg (norm_nonneg (ℓ h₁-ℓ h₂)) (norm_nonneg (ξ₁-ξ₂))
  · intro h ω R hh hω hR he
    exact hres (ℓ h) ω R (hctrl h _ hh hω).2.2.2.2.2.2.2.2
      (hctrl h _ hh hR).2.2.2.2.2.2.2.2 he

end NonSymmetricDyson.Full.Nonlinear
