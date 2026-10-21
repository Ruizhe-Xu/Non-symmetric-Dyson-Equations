import Dyson.Full.NonlinearGeometry
import Dyson.Full.NonlinearDenominator
import Dyson.Full.NonlinearPoint
import Dyson.Full.NonlinearLargeError
import Dyson.GlobalWellPosedness

/-! The boundary part of M7 with uniform, explicit quantifier order.
All neighborhood, anchor, and comparison constants are chosen before the
real energy, height, error size, and continuous approximate family. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1600000 in
/-- The full nonlinear edge/cusp estimate from the constructed local reduction.
The anchor comes from actual interior stability at one fixed height. -/
theorem nonlinear_boundary_main_of_reduction_below
    (Hmax : ℝ) (hHmax : 0 < Hmax)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (τ : ℝ) (m : ℂ → (ι → ℂ)) (mτ p q v : ι → ℂ)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (k : ℕ) (hk : 2 ≤ k) (D : LocalReduction F K ℓ p q v k)
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hmτ : BasicEstimates.IsDysonSolution S a (τ:ℂ) mτ)
    (hmτ0 : ∀ i, mτ i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i^2=1) (hq : ∀ i, q i=p i*mτ i)
    (hmvalue : m (τ:ℂ)=mτ)
    (hmcont : ContinuousWithinAt m {z:ℂ | 0 ≤ z.im} (τ:ℂ))
    (hm : ∀ z:ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heqm : ∀ z:ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z)) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ H ≤ Hmax ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η E : ℝ) (g : ℝ → (ι → ℂ)),
        |x-τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E → ContinuousOn g (Icc η H) →
        (∀ t ∈ Icc η H, ∀ i, g t i ≠ 0) →
        (∀ t ∈ Icc η H, ‖g t-m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η H, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η-m (verticalPoint x η)‖ ≤
          C*E/(E+‖verticalPoint x η-(τ:ℂ)‖)^(1-(1:ℝ)/k) := by
  have hrad := D.radius_pos
  have hsep := D.separation_pos
  have hresC := D.residualConstant_pos
  have hLip := D.lipschitzConstant_pos
  have hR := D.roughConstant_pos
  have hkpos : 0 < k := by omega
  have hp0 : 0 < (1:ℝ)/k := by positivity
  have hp1 : (1:ℝ)/k < 1 := by
    have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
    apply (div_lt_one (by positivity : (0:ℝ)<k)).mpr
    linarith
  obtain ⟨δd,hδd,hdenSmall⟩ := rootDenominator_small D.separation k hk
  let δ := min δd (min D.rootRadius (min (D.radius/4) Hmax))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδd (lt_min D.rootRadius_pos (lt_min (by positivity) hHmax))
  have hδd' : δ ≤ δd := min_le_left _ _
  have hδroot : δ ≤ D.rootRadius := (min_le_right _ _).trans (min_le_left _ _)
  have hδforcing : δ ≤ D.radius/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδheight : δ ≤ Hmax :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨H,r,cg,hH,hr,hcg,hgeometry⟩ :=
    normalized_uniform_rectangle m q mτ τ δ D.radius hδ D.radius_pos hmvalue hmcont
  have hHmax' : H ≤ Hmax := by
    have hh := (hgeometry τ H (m (verticalPoint τ H)) (by simpa using hr.le) hH.le le_rfl
      (by simpa using hcg.le)).1
    have hi : H ≤ ‖verticalPoint τ H - (τ : ℂ)‖ := by
      simpa [verticalPoint] using Complex.im_le_norm (verticalPoint τ H - (τ : ℂ))
    exact (hi.trans hh.le).trans hδheight
  obtain ⟨ca,Ca,hca,hCa,hanchorBound⟩ :=
    fixed_height_scalar_anchor S a τ r H ℓ q mτ hS hr.le hH
  let c₀ := min cg ca
  have hc₀ : 0 < c₀ := lt_min hcg hca
  let A := 1+D.residualConstant+Ca
  have hA : 0 < A := by dsimp [A]; positivity
  have hAres : D.residualConstant ≤ A := by dsimp [A]; linarith
  have hAa : Ca ≤ A := by dsimp [A]; linarith [D.residualConstant_pos]
  let cstar := (D.separation^(k+1)/(2:ℝ)^(k-1))/(4*A)
  have hcstar : 0 < cstar := by dsimp [cstar]; positivity
  let Rough := 1+2*‖q‖*D.roughConstant
  have hRough : 0 < Rough := by dsimp [Rough]; positivity
  let B0 := ‖q‖*((‖v‖+D.lipschitzConstant)*A+D.lipschitzConstant)
  let factor := (2:ℝ)^(k-1)/(D.separation*D.separation^(k-1))
  let Fine := 1+B0*factor
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  have hFine : 0 < Fine := by dsimp [Fine]; positivity
  let Cs := PowerGluing.gluingConstant Rough Fine cstar ((1:ℝ)/k)
  have hCs : 0 < Cs := PowerGluing.gluingConstant_pos hRough hcstar
  obtain ⟨Cl,hCl,hlarge⟩ := PowerGluing.large_error_uniform_bound
    (c₀ := c₀) (δ := δ) (ε := D.radius/4) (p := (1:ℝ)/k)
    hc₀ hδ (by positivity) hp0
  let C := 1+max Cs Cl
  have hC : 0 < C := by dsimp [C]; have hh := le_max_left Cs Cl; linarith
  refine ⟨H,r,c₀,C,hH,hHmax',hr,hc₀,hC,?_⟩
  intro x η E g hx hη hηH hE hgcont hg0 hclose hres
  have hηmem : η ∈ Icc η H := ⟨le_rfl,hηH⟩
  let z := verticalPoint x η
  let d := ‖z-(τ:ℂ)‖
  have hz : 0 < z.im := hη
  have hd : 0 < d := by
    apply norm_pos_iff.mpr
    intro he
    have hh := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.ofReal_im] at hh
    exact hη.ne' hh
  have hgeo : ∀ t ∈ Icc η H,
      ‖verticalPoint x t-(τ:ℂ)‖ < δ ∧
      ‖normalized q mτ (m (verticalPoint x t))‖ < D.radius/2 ∧
      ‖normalized q mτ (g t)‖ < D.radius := by
    intro t ht
    exact hgeometry x t (g t) hx (hη.le.trans ht.1) ht.2
      ((hclose t ht).trans (min_le_left _ _))
  have hdδ : d ≤ δ := (hgeo η hηmem).1.le
  have hscale : 0 ≤ E/(E+d)^(1-(1:ℝ)/k) :=
    div_nonneg hE (Real.rpow_nonneg (by positivity) _)
  have hcommon : ∀ B : ℝ, B ≤ C →
      ‖g η-m z‖ ≤ B*E/(E+d)^(1-(1:ℝ)/k) →
      ‖g η-m z‖ ≤ C*E/(E+d)^(1-(1:ℝ)/k) := by
    intro B hBC hb
    calc
      _ ≤ B*(E/(E+d)^(1-(1:ℝ)/k)) := by simpa only [mul_div_assoc] using hb
      _ ≤ C*(E/(E+d)^(1-(1:ℝ)/k)) := mul_le_mul_of_nonneg_right hBC hscale
      _ = _ := by ring
  by_cases hbig : D.radius/4 ≤ E
  · apply hcommon Cl (by dsimp [C]; have hh := le_max_right Cs Cl; linarith)
    exact hlarge E d ‖g η-m z‖ hbig hd.le hdδ (hclose η hηmem)
  have hEsmall : E < D.radius/4 := lt_of_not_ge hbig
  have hone : ‖(1:ι→ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)
  have hωbound : ∀ t, ‖(verticalPoint x t-(τ:ℂ)) • (1:ι→ℂ)‖ ≤
      ‖verticalPoint x t-(τ:ℂ)‖ := by
    intro t
    rw [norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (norm_nonneg _)
  have hξm : ∀ t ∈ Icc η H,
      ‖(verticalPoint x t-(τ:ℂ)) • (1:ι→ℂ)‖ < D.radius := by
    intro t ht
    have hh := (hωbound t).trans_lt ((hgeo t ht).1.trans_le hδforcing)
    linarith [D.radius_pos]
  have hξg : ∀ t ∈ Icc η H,
      ‖(verticalPoint x t-(τ:ℂ)) • (1:ι→ℂ)+Model.residual S a (verticalPoint x t) (g t)‖ < D.radius := by
    intro t ht
    have hh := (norm_add_le ((verticalPoint x t-(τ:ℂ)) • (1:ι→ℂ))
      (Model.residual S a (verticalPoint x t) (g t))).trans (add_le_add (hωbound t) (hres t ht))
    have hb := (hgeo t ht).1.trans_le hδforcing
    linarith [D.radius_pos]
  have hrough : cstar*d < E → ‖g η-m z‖ ≤ Rough*(E+d)^((1:ℝ)/k) := by
    intro _
    have hh := actual_point_rough_bound S a (τ:ℂ) z mτ (m z) (g η) p q v F K ℓ k D
      hF hmτ hmτ0 hq0 hp hq (hm z hz) (heqm z hz) (hg0 η hηmem)
      (hgeo η hηmem).2.2 ((hgeo η hηmem).2.1.trans (by linarith [D.radius_pos]))
      (hξg η hηmem) (hξm η hηmem) E hE (hres η hηmem)
    calc
      _ ≤ (2*‖q‖*D.roughConstant)*(E+d)^((1:ℝ)/k) := by simpa only [add_comm] using hh
      _ ≤ Rough*(E+d)^((1:ℝ)/k) :=
        mul_le_mul_of_nonneg_right (by dsimp [Rough]; linarith) (Real.rpow_nonneg (by positivity) _)
  have hfine : E ≤ cstar*d → ‖g η-m z‖ ≤ Fine*E/d^(1-(1:ℝ)/k) := by
    intro hregime
    let X := Icc η H
    letI : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_Icc
    let zpath : X → ℂ := fun t => verticalPoint x t.val
    let gpath : X → (ι→ℂ) := fun t => g t.val
    let mpath : X → (ι→ℂ) := fun t => m (zpath t)
    have hzp : Continuous zpath := (verticalPoint_continuous x).comp continuous_subtype_val
    have hgp : Continuous gpath := continuousOn_iff_continuous_restrict.mp hgcont
    have hmc : ContinuousOn m {z:ℂ | 0 < z.im} := by
      apply (GlobalWellPosedness.solution_continuousOn a hS).congr
      intro z hz
      exact (GlobalWellPosedness.solution_eq_of_upper_solution a hS hz (hm z hz) (heqm z hz)).symm
    have hmp : Continuous mpath := hmc.comp_continuous hzp
      (fun t => hη.trans_le t.property.1)
    have hzpath : ∀ t:X, 0 < (zpath t).im := fun t => hη.trans_le t.property.1
    have hrootSmall : ∀ t:X, ‖zpath t-(τ:ℂ)‖ < D.rootRadius :=
      fun t => (hgeo t.val t.property).1.trans_le hδroot
    have hden : ∀ t:X, rootDenominator D.separation k (zpath t-(τ:ℂ)) ≤ 1 :=
      fun t => hdenSmall _ ((hgeo t.val t.property).1.trans_le hδd')
    have hgap : ∀ t:X, 2*(A*E) <
        (D.separation*‖zpath t-(τ:ℂ)‖^((1:ℝ)/k))*rootDenominator D.separation k (zpath t-(τ:ℂ)) := by
      intro t
      exact rootDenominator_gap D.separation A E d D.separation_pos hA hd k hkpos _
        (verticalPoint_norm_sub_mono x τ η t.val hη.le t.property.1) hregime
    let top : X := ⟨H,⟨hηH,le_rfl⟩⟩
    have hanchor : ‖ℓ (normalized q mτ (gpath top))-ℓ (normalized q mτ (mpath top))‖ ≤
        (A*E)/rootDenominator D.separation k (zpath top-(τ:ℂ)) := by
      have ha := hanchorBound (zpath top) (mpath top) (gpath top) E hx rfl
        (hm _ (hzpath top)) (heqm _ (hzpath top))
        ((hclose H top.property).trans (min_le_right _ _)) (hres H top.property)
      have hpden := rootDenominator_pos D.separation D.separation_pos k (zpath top-(τ:ℂ))
        (by intro hh; have hh' := congrArg Complex.im hh; simp at hh'; exact hH.ne' hh')
      calc
        _ ≤ Ca*E := ha
        _ ≤ A*E := mul_le_mul_of_nonneg_right hAa hE
        _ ≤ (A*E)/rootDenominator D.separation k (zpath top-(τ:ℂ)) := by
          apply (le_div_iff₀ hpden).mpr
          have hh := mul_le_mul_of_nonneg_left (hden top) (mul_nonneg hA.le hE)
          simpa using hh
    have hpath := actual_model_connected_path_bound S a τ mτ p q v F K ℓ k hkpos D
      hF hmτ hmτ0 hq0 hp hq zpath gpath mpath hzp hgp hmp hzpath
      (fun t => hm _ (hzpath t)) (fun t => heqm _ (hzpath t)) (fun t => hg0 t.val t.property)
      hrootSmall (fun t => (hgeo t.val t.property).2.2)
      (fun t => (hgeo t.val t.property).2.1.trans (by linarith [D.radius_pos]))
      (fun t => hξg t.val t.property) (fun t => hξm t.val t.property)
      E A hE hA hAres (fun t => hres t.val t.property) hgap hden top hanchor
    have hh := hpath ⟨η,hηmem⟩
    change ‖g η-m z‖ ≤ B0*E/rootDenominator D.separation k (z-(τ:ℂ)) at hh
    rw [mul_div_assoc, rootDenominator,
      PowerGluing.fine_radius_identity (norm_nonneg _) k hkpos] at hh
    calc
      _ ≤ (B0*factor)*(E/d^(1-(1:ℝ)/k)) := by convert hh using 1 <;> ring
      _ ≤ Fine*(E/d^(1-(1:ℝ)/k)) := mul_le_mul_of_nonneg_right
        (by dsimp [Fine]; linarith) (div_nonneg hE (Real.rpow_nonneg hd.le _))
      _ = _ := by ring
  apply hcommon Cs (by dsimp [C]; have hh := le_max_left Cs Cl; linarith)
  simpa only [mul_div_assoc] using PowerGluing.two_regime_gluing_positive_background
    hE hd hcstar hp0 hp1 hRough.le hFine.le hrough hfine

/-- The fixed-height form, obtained by choosing any positive height cap. -/
theorem nonlinear_boundary_main_of_reduction
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (τ : ℝ) (m : ℂ → (ι → ℂ)) (mτ p q v : ι → ℂ)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (k : ℕ) (hk : 2 ≤ k) (D : LocalReduction F K ℓ p q v k)
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hmτ : BasicEstimates.IsDysonSolution S a (τ:ℂ) mτ)
    (hmτ0 : ∀ i, mτ i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i^2=1) (hq : ∀ i, q i=p i*mτ i)
    (hmvalue : m (τ:ℂ)=mτ)
    (hmcont : ContinuousWithinAt m {z:ℂ | 0 ≤ z.im} (τ:ℂ))
    (hm : ∀ z:ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heqm : ∀ z:ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z)) :
    ∃ H r c₀ C : ℝ, 0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η E : ℝ) (g : ℝ → (ι → ℂ)),
        |x-τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E → ContinuousOn g (Icc η H) →
        (∀ t ∈ Icc η H, ∀ i, g t i ≠ 0) →
        (∀ t ∈ Icc η H, ‖g t-m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η H, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η-m (verticalPoint x η)‖ ≤
          C*E/(E+‖verticalPoint x η-(τ:ℂ)‖)^(1-(1:ℝ)/k) := by
  obtain ⟨H,r,c₀,C,hH,_,hr,hc₀,hC,hb⟩ := nonlinear_boundary_main_of_reduction_below 1 zero_lt_one
    S a hS τ m mτ p q v F K ℓ k hk D hF hmτ hmτ0 hq0 hp hq hmvalue hmcont hm heqm
  exact ⟨H,r,c₀,C,hH,hr,hc₀,hC,hb⟩

end NonSymmetricDyson.Full.Nonlinear
