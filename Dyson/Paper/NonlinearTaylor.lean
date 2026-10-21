import Dyson.Full.NonlinearAssembly

/-! Explicit derivative and Taylor calculations in Step 1 of the original
M7 proof. The expansion is derived from the exact fixed-point identity. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.Nonlinear
open Full.Nonlinear
variable {ι : Type*} [Fintype ι]

/-- The first differential of the stable map: the Θ derivative vanishes,
and the derivative in any forcing direction ξ is K(qξ). -/
theorem stable_map_first_derivative
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (hWa : AnalyticAt ℂ W 0) (hW0 : W 0 = 0)
    (hfix : ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
      W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2))
    (a : ℂ) (ξ : ι → ℂ) :
    HasDerivAt (fun t : ℂ => W (t * a, t • ξ)) (K (q * ξ)) 0 := by
  let H : ℂ → ι → ℂ := fun t => (t*a) • r + W (t*a,t • ξ)
  have hline : HasDerivAt (fun t : ℂ => (t*a,t • ξ)) (a,ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const a).prodMk
      ((hasDerivAt_id (0 : ℂ)).smul_const ξ)
  have hW00 : W (0,0) = 0 := hW0
  have hw : HasDerivAt (fun t : ℂ => W (t*a,t • ξ))
      ((fderiv ℂ W 0) (a,ξ)) 0 := by
    have hw0 : HasFDerivAt W (fderiv ℂ W 0) ((0 : ℂ)*a, (0 : ℂ) • ξ) := by
      simpa using hWa.differentiableAt.hasFDerivAt
    exact hw0.comp_hasDerivAt 0 hline
  have hH := (((hasDerivAt_id (0 : ℂ)).mul_const a).smul_const r).add hw
  have hH0 : H 0 = 0 := by simp [H,hW00]
  have hp := hasDerivAt_const (0 : ℂ) p
  have hq := hasDerivAt_const (0 : ℂ) q
  have hQ := (hp.mul hH).mul (F.hasFDerivAt.comp_hasDerivAt 0 hH)
  have hN := hQ.add ((hq.mul ((hasDerivAt_const (0 : ℂ) (1 : ι → ℂ)).add
    (hp.mul hH))).mul ((hasDerivAt_id (0 : ℂ)).smul_const ξ))
  have hh := K.hasFDerivAt.comp_hasDerivAt 0 hN
  have hder : HasDerivAt (fun t : ℂ =>
      K (quadraticNonlinearity F p q (H t) (t • ξ))) (K (q*ξ)) 0 := by
    convert hh using 1 <;> simp [quadraticNonlinearity,H,hW00,Function.comp_def]
  apply hder.congr_of_eventuallyEq
  have ht : Tendsto (fun t : ℂ => (t*a,t • ξ)) (𝓝 0) (𝓝 0) := by
    simpa using hline.continuousAt.tendsto
  exact ht.eventually hfix

/-- Differentiate the actual quadratic term twice. The unknown second
 derivative of h cancels because h(0)=0. -/
theorem quadratic_map_second_derivative
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p r : ι → ℂ)
    (h : ℂ → ι → ℂ) (ha : AnalyticAt ℂ h 0) (h0 : h 0=0)
    (hd : deriv h 0=r) :
    HasDerivAt (deriv (fun t => K (p*h t*F (h t))))
      (2 • K (p*r*F r)) 0 := by
  let Q : ℂ → ι → ℂ := fun t => K (p*h t*F (h t))
  let Q' : ℂ → ι → ℂ := fun t =>
    K (p*deriv h t*F (h t)+p*h t*F (deriv h t))
  have he : deriv Q =ᶠ[𝓝 0] Q' := by
    filter_upwards [ha.eventually_analyticAt] with t ht
    have hh := ht.differentiableAt.hasDerivAt
    have hq := K.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_const t p).mul hh).mul (F.hasFDerivAt.comp_hasDerivAt t hh))
    simpa [Q,Q'] using hq.deriv
  have hh := ha.differentiableAt.hasDerivAt
  have hhd := ha.deriv.differentiableAt.hasDerivAt
  have hq := K.hasFDerivAt.comp_hasDerivAt 0
    ((((hasDerivAt_const (0 : ℂ) p).mul hhd).mul
      (F.hasFDerivAt.comp_hasDerivAt 0 hh)).add
      (((hasDerivAt_const (0 : ℂ) p).mul hh).mul
      (F.hasFDerivAt.comp_hasDerivAt 0 hhd)))
  have hq' : HasDerivAt Q' (2 • K (p*r*F r)) 0 := by
    convert hq using 1 <;> simp [Q',h0,hd,two_smul]
  exact hq'.congr_of_eventuallyEq he

/-- The second Θ derivative asserted in the manuscript. Together with the
first derivative this identifies the complete pure quadratic Taylor jet. -/
theorem stable_map_second_derivative
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r : ι → ℂ)
    (hFr : F r=r)
    (W : ℂ × (ι → ℂ) → (ι → ℂ)) (hWa : AnalyticAt ℂ W 0) (hW0 : W 0=0)
    (hfix : ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
      W v = K (quadraticNonlinearity F p q (v.1 • r + W v) v.2)) :
    HasDerivAt (deriv (fun t : ℂ => W (t,0))) (2 • K (p*r*r)) 0 := by
  let w : ℂ → ι → ℂ := fun t => W (t,0)
  let h : ℂ → ι → ℂ := fun t => t • r+w t
  have hW00 : W (0,0)=0 := hW0
  have hw : HasDerivAt w 0 0 := by
    simpa [w] using stable_map_first_derivative F K p q r W hWa hW0 hfix 1 0
  have hha : AnalyticAt ℂ h 0 := by
    have hw' : AnalyticAt ℂ w 0 := by
      have hl : AnalyticAt ℂ (fun t : ℂ => (t,(0 : ι → ℂ))) 0 :=
        analyticAt_id.prod analyticAt_const
      exact hWa.comp_of_eq hl rfl
    exact (analyticAt_id.smul analyticAt_const).add hw'
  have hh0 : h 0=0 := by simp [h,w,hW00]
  have hhd : deriv h 0=r := by
    simpa [h,w] using (((hasDerivAt_id (0 : ℂ)).smul_const r).add hw).deriv
  have ht : Tendsto (fun t : ℂ => (t,(0 : ι → ℂ))) (𝓝 0) (𝓝 0) := by
    exact continuousAt_id.prodMk continuousAt_const
  have he : w =ᶠ[𝓝 0] (fun t => K (p*h t*F (h t))) := by
    filter_upwards [ht.eventually hfix] with t hh
    simpa [w,h,quadraticNonlinearity] using hh
  have hq := quadratic_map_second_derivative F K p r h hha hh0 hhd
  rw [hFr] at hq
  exact hq.congr_of_eventuallyEq he.deriv

/-- The complete mixed Taylor remainder, equation (expansion-Wtau).
All constants are actual operator/vector norms. -/
theorem stable_map_second_order_taylor
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q r w ξ : ι → ℂ) (θ : ℂ)
    (hFr : F r = r)
    (hw : w = K (quadraticNonlinearity F p q (θ • r + w) ξ))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hD₁ : ‖p‖ * ‖r‖ * (‖F‖ + 1) ≤ D)
    (hD₂ : ‖p‖ * ‖F‖ ≤ D)
    (hD₃ : ‖q‖ * ‖p‖ * (‖r‖ + 1) ≤ D)
    (hθ : ‖θ‖ ≤ 1) (hsize : ‖w‖ ≤ C * (‖θ‖ ^ 2 + ‖ξ‖)) :
    ‖w - θ ^ 2 • K (p * r * r) - K (q * ξ)‖ ≤
      ‖K‖ * D * (1 + 2 * C + 2 * C ^ 2) *
        (‖θ‖ ^ 3 + ‖θ‖ * ‖ξ‖ + ‖ξ‖ ^ 2) := by
  rw [stable_fixed_point_remainder_identity F K p q r w ξ θ hFr hw]
  have hv := mixed_remainder_norm_bound F p q r w w ξ θ D hD hD₁ hD₂ hD₃
  have hm := stable_remainder_majorant (norm_nonneg θ) hθ (norm_nonneg ξ)
    (norm_nonneg w) hC hsize
  calc
    _ ≤ ‖K‖ * ‖θ • (p*r*F w+p*w*r)+p*w*F w+q*p*(θ • r+w)*ξ‖ := K.le_opNorm _
    _ ≤ ‖K‖ * (D * (‖θ‖*‖w‖+‖w‖^2+(‖θ‖+‖w‖)*‖ξ‖)) := by gcongr
    _ ≤ ‖K‖ * (D * ((1+2*C+2*C^2)*(‖θ‖^3+‖θ‖*‖ξ‖+‖ξ‖^2))) := by gcongr
    _ = _ := by ring

end NonSymmetricDyson.Paper.Nonlinear
