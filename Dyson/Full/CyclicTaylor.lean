import Dyson.Full.CyclicGeneralLimit

/-! Explicit second-order remainder for the cycle example.  It follows from
an exact quadratic identity and the first derivative, with no Taylor estimate
assumed as an external input. -/

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.CyclicGeneral
open CyclicExample (scalar)

theorem scalar_second_order_remainder (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ z in 𝓝 (((-2*w.re : ℝ) : ℂ)),
      ‖scalar z-w-(-w/((2*w.im : ℂ)*Complex.I))*(z-((-2*w.re : ℝ) : ℂ))‖ ≤
        C*‖z-((-2*w.re : ℝ) : ℂ)‖^2 := by
  let τ : ℂ := ((-2*w.re : ℝ) : ℂ)
  let c : ℂ := (2*w.im : ℂ)*Complex.I
  have hc : c≠0 := mul_ne_zero
    (by exact_mod_cast (mul_pos (by norm_num : (0 : ℝ)<2) hi).ne') Complex.I_ne_zero
  have hcpos : 0<‖c‖ := norm_pos_iff.mpr hc
  have hcoef : 2*w+τ=c := by apply Complex.ext <;> simp [τ,c] <;> ring
  have hwquad : w^2+τ*w+1=0 := by
    have hs : scalar τ=w := CyclicExample.scalar_at_unit_energy w hw hi
    simpa only [hs] using CyclicExample.scalar_quadratic τ
  obtain ⟨B,hB,hbound⟩ :=
    (CyclicExample.scalar_hasDerivAt_unit_energy w hw hi).isBigO_sub.exists_pos
  refine ⟨B*(B+1)/‖c‖,by positivity,?_⟩
  filter_upwards [hbound.bound] with z hz
  rw [CyclicExample.scalar_at_unit_energy w hw hi] at hz
  have he : (scalar z-w-(-w/c)*(z-τ))*c =
      -(scalar z-w)*(scalar z-w+(z-τ)) := by
    calc
      _ = (scalar z-w)*c+w*(z-τ) := by field_simp; ring
      _ = _ := by
        rw [← hcoef]
        linear_combination CyclicExample.scalar_quadratic z - hwquad
  have hsum : ‖scalar z-w+(z-τ)‖≤(B+1)*‖z-τ‖ := by
    calc
      _ ≤ ‖scalar z-w‖+‖z-τ‖ := norm_add_le _ _
      _ ≤ B*‖z-τ‖+‖z-τ‖ := add_le_add_right hz _
      _ = _ := by ring
  have hprod : ‖scalar z-w-(-w/c)*(z-τ)‖*‖c‖≤B*(B+1)*‖z-τ‖^2 := by
    calc
      _ = ‖(scalar z-w-(-w/c)*(z-τ))*c‖ := (norm_mul _ _).symm
      _ = ‖scalar z-w‖*‖scalar z-w+(z-τ)‖ := by rw [he,norm_mul,norm_neg]
      _ ≤ (B*‖z-τ‖)*((B+1)*‖z-τ‖) :=
        mul_le_mul hz hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  change ‖scalar z-w-(-w/c)*(z-τ)‖≤(B*(B+1)/‖c‖)*‖z-τ‖^2
  calc
    _ ≤ B*(B+1)*‖z-τ‖^2/‖c‖ := (le_div_iff₀ hcpos).mpr hprod
    _ = _ := by ring

/-- The literal local expansion from the article, including a quantified
quadratic error bound uniform over sufficiently small positive heights. -/
theorem scalar_vertical_taylor (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ η : ℝ, 0<η → η<r →
      ‖scalar (heightPoint (-2*w.re) η)-w*(1-(η : ℂ)/(2*w.im : ℂ))‖≤C*η^2 := by
  obtain ⟨C,hC,hbound⟩ := scalar_second_order_remainder w hw hi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨C,r,hC,hr,?_⟩
  intro η hη hηr
  have hz : heightPoint (-2*w.re) η ∈ Metric.ball (((-2*w.re : ℝ) : ℂ)) r := by
    simpa only [Metric.mem_ball,dist_eq_norm,heightPoint_distance _ _ hη.le] using hηr
  have hb := hball hz
  dsimp only [Set.mem_setOf_eq] at hb
  rw [heightPoint_distance _ _ hη.le] at hb
  convert hb using 1
  congr 1
  unfold heightPoint
  have him0 : (w.im : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hi.ne'
  field_simp
  ring

end NonSymmetricDyson.Full.CyclicGeneral
