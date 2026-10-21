import Dyson.Full.NonlinearModel

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

def verticalPoint (x t : ℝ) : ℂ := ⟨x,t⟩

@[simp] theorem verticalPoint_re (x t : ℝ) : (verticalPoint x t).re=x := rfl
@[simp] theorem verticalPoint_im (x t : ℝ) : (verticalPoint x t).im=t := rfl

theorem verticalPoint_continuous (x : ℝ) : Continuous (verticalPoint x) := by
  have he : verticalPoint x = fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I := by
    funext t
    apply Complex.ext <;> simp [verticalPoint]
  rw [he]
  fun_prop

theorem verticalPoint_norm_sub_le (x τ t : ℝ) (ht : 0 ≤ t) :
    ‖verticalPoint x t-(τ:ℂ)‖ ≤ |x-τ|+t := by
  simpa [abs_of_nonneg ht] using Complex.norm_le_abs_re_add_abs_im
    (verticalPoint x t-(τ:ℂ))

theorem verticalPoint_norm_sub_mono (x τ s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖verticalPoint x s-(τ:ℂ)‖ ≤ ‖verticalPoint x t-(τ:ℂ)‖ := by
  have h₁ := Complex.sq_norm (verticalPoint x s-(τ:ℂ))
  have h₂ := Complex.sq_norm (verticalPoint x t-(τ:ℂ))
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, verticalPoint_re, verticalPoint_im] at h₁ h₂
  nlinarith [norm_nonneg (verticalPoint x s-(τ:ℂ)), norm_nonneg (verticalPoint x t-(τ:ℂ))]

theorem normalized_difference_bound (q mτ g m : ι → ℂ) :
    ‖normalized q mτ g-normalized q mτ m‖ ≤ ‖q⁻¹‖*‖g-m‖ := by
  have he : normalized q mτ g-normalized q mτ m = (g-m)*q⁻¹ := by
    ext i
    simp only [normalized, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    ring
  rw [he]
  exact (norm_mul_le _ _).trans_eq (mul_comm _ _)

/-- Continuity at the boundary chooses one height, one real interval, and one
absolute closeness radius, before any approximate solution is supplied. -/
theorem normalized_uniform_rectangle
    (m : ℂ → (ι → ℂ)) (q mτ : ι → ℂ) (τ δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hmτ : m (τ:ℂ)=mτ)
    (hmcont : ContinuousWithinAt m {z:ℂ | 0 ≤ z.im} (τ:ℂ)) :
    ∃ H r c : ℝ, 0 < H ∧ 0 < r ∧ 0 < c ∧
      ∀ (x t : ℝ) (g : ι → ℂ), |x-τ| ≤ r → 0 ≤ t → t ≤ H →
      ‖g-m (verticalPoint x t)‖ ≤ c →
      ‖verticalPoint x t-(τ:ℂ)‖ < δ ∧
      ‖normalized q mτ (m (verticalPoint x t))‖ < ε/2 ∧
      ‖normalized q mτ g‖ < ε := by
  have hn : ContinuousWithinAt (fun z => normalized q mτ (m z))
      {z:ℂ | 0 ≤ z.im} (τ:ℂ) :=
    (hmcont.sub continuousWithinAt_const).mul continuousWithinAt_const
  have hev : ∀ᶠ z in 𝓝[{z:ℂ | 0 ≤ z.im}] (τ:ℂ),
      ‖normalized q mτ (m z)‖ < ε/2 :=
    hn.norm.eventually (gt_mem_nhds (by simpa [hmτ,normalized,div_eq_mul_inv] using (half_pos hε)))
  obtain ⟨b,hb,hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let H := min δ b / 4
  let c := ε/(4*(‖q⁻¹‖+1))
  have hH : 0 < H := by dsimp [H]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨H,H,c,hH,hH,hc,?_⟩
  intro x t g hx ht htH hg
  have hz : ‖verticalPoint x t-(τ:ℂ)‖ < min δ b := by
    have hn := verticalPoint_norm_sub_le x τ t ht
    dsimp [H] at hx htH
    have hbmin : 0 < min δ b := lt_min hδ hb
    nlinarith
  have hsmall : ‖normalized q mτ (m (verticalPoint x t))‖ < ε/2 :=
    hball ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hz.trans_le (min_le_right _ _),ht⟩
  refine ⟨hz.trans_le (min_le_left _ _),hsmall,?_⟩
  have hcprod : ‖q⁻¹‖*c < ε/4 := by
    dsimp [c]
    have hden : 0 < 4*(‖q⁻¹‖+1) := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith
  have hd := (normalized_difference_bound q mτ g (m (verticalPoint x t))).trans
    (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
  have htri := norm_add_le (normalized q mτ g-normalized q mτ (m (verticalPoint x t)))
    (normalized q mτ (m (verticalPoint x t)))
  rw [sub_add_cancel] at htri
  linarith

end NonSymmetricDyson.Full.Nonlinear
