import Dyson.Full.ExternalSpectral
import Dyson.Full.EuclideanInverse

noncomputable section
namespace NonSymmetricDyson.Full.Spectral
open EuclideanInverse
variable {ι : Type*} [Fintype ι] {A : End ι}
namespace SimpleSpectralSplit

theorem euclidean_inverse_left (d : SimpleSpectralSplit A) (hβ : d.value≠0)
    (x : EuclideanSpace ℂ ι) : conjugate d.inverse (conjugate A x)=x := by
  change WithLp.toLp 2 (d.inverse (A (WithLp.ofLp x)))=x
  rw [d.inverse_left hβ]
  rfl

theorem euclidean_inverse_right (d : SimpleSpectralSplit A) (hβ : d.value≠0)
    (x : EuclideanSpace ℂ ι) : conjugate A (conjugate d.inverse x)=x := by
  change WithLp.toLp 2 (A (d.inverse (WithLp.ofLp x)))=x
  rw [d.inverse_right hβ]
  rfl

theorem euclidean_inverse_norm_lower (d : SimpleSpectralSplit A) :
    ‖d.value‖⁻¹ ≤ ‖conjugate d.inverse‖ := by
  have hh := (conjugate d.inverse).le_opNorm (WithLp.toLp 2 d.right)
  rw [conjugate_apply,d.inverse_apply_right] at hh
  have he : WithLp.toLp 2 (d.value⁻¹ • d.right)=d.value⁻¹ • WithLp.toLp 2 d.right := rfl
  rw [he,norm_smul,norm_inv] at hh
  have hn : 0 < ‖WithLp.toLp 2 d.right‖ := norm_pos_iff.mpr (by
    intro h
    apply d.right_ne_zero
    exact congrArg (WithLp.ofLp) h)
  exact le_of_mul_le_mul_right hh hn

theorem euclidean_stable_bound (d : SimpleSpectralSplit A) (C : ℝ)
    (h : ‖d.projector‖+‖ContinuousLinearMap.id ℂ (Vec ι)-d.projector‖+‖d.stable‖ ≤ C) :
    ‖conjugate d.projector‖+
      ‖conjugate (ContinuousLinearMap.id ℂ (Vec ι)-d.projector)‖+
      ‖conjugate d.stable‖+‖(conjugate d.stable).adjoint‖ ≤
      2*Real.sqrt (Fintype.card ι)*C := by
  have hp := conjugate_norm_upper d.projector
  have hq := conjugate_norm_upper (ContinuousLinearMap.id ℂ (Vec ι)-d.projector)
  have hk := conjugate_norm_upper d.stable
  have ha : ‖(conjugate d.stable).adjoint‖=‖conjugate d.stable‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  rw [ha]
  have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (Fintype.card ι))
  nlinarith [norm_nonneg d.projector,
    norm_nonneg (ContinuousLinearMap.id ℂ (Vec ι)-d.projector), Real.sqrt_nonneg (Fintype.card ι)]

theorem euclidean_inverse_norm_upper (d : SimpleSpectralSplit A) (hβ : d.value≠0)
    (ρ C : ℝ) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hval : ‖d.value‖ ≤ ρ)
    (hP : ‖d.projector‖ ≤ C) (hK : ‖d.stable‖ ≤ C) :
    ‖conjugate d.inverse‖ ≤ (Real.sqrt (Fintype.card ι)*C*(1+ρ))/‖d.value‖ := by
  have hn : 0 < ‖d.value‖ := norm_pos_iff.mpr hβ
  have hh : ‖d.inverse‖ ≤ C*(1+ρ)/‖d.value‖ := by
    apply d.inverse_norm_upper.trans
    apply (le_div_iff₀ hn).mpr
    have he : ‖d.value‖⁻¹*‖d.value‖=1 := inv_mul_cancel₀ hn.ne'
    calc
      (‖d.value‖⁻¹*‖d.projector‖+‖d.stable‖)*‖d.value‖ =
          ‖d.projector‖+‖d.stable‖*‖d.value‖ := by nlinarith
      _ ≤ C+C*ρ := add_le_add hP (mul_le_mul hK hval (norm_nonneg _) hC)
      _ = C*(1+ρ) := by ring
  exact (conjugate_norm_upper _).trans
    ((mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq (by ring))

end SimpleSpectralSplit
end NonSymmetricDyson.Full.Spectral
