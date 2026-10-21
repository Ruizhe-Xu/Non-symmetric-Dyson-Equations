import Dyson.Paper.SpectralResidual

/-! Original Step 4 absorption on the moving stable subspace.
This estimate is derived from the actual base inverse and a nearby left
functional, without assuming a bound on the perturbed stable inverse. -/
noncomputable section
namespace NonSymmetricDyson.Paper.Spectral
open Full.Spectral
variable {ι : Type*} [Fintype ι]

theorem moving_complement_coercivity (A E K : End ι) (r : Vec ι) (l v : Dual ι)
    (hKA : ∀ x,K (A x)=x-l x • r)
    (B : ℝ) (hB : 0≤B) (hK : ‖K‖≤B)
    (hsmall : ‖v-l‖*‖r‖+B*‖E‖≤1/2)
    (x : Vec ι) (hx : v x=0) : ‖x‖≤2*B*‖(A+E) x‖ := by
  have hlx : ‖l x‖≤‖v-l‖*‖x‖ := by
    have h := (v-l).le_opNorm x
    simpa [ContinuousLinearMap.sub_apply,hx] using h
  have hid : x=l x • r+K ((A+E) x)-K (E x) := by
    rw [ContinuousLinearMap.add_apply,map_add,hKA]
    abel
  have hnorm : ‖x‖≤B*‖(A+E) x‖+(‖v-l‖*‖r‖+B*‖E‖)*‖x‖ := by
    calc
      ‖x‖ = ‖l x • r+K ((A+E) x)-K (E x)‖ := congrArg norm hid
      _ ≤ ‖l x‖*‖r‖+‖K ((A+E) x)‖+‖K (E x)‖ := by
        have h := norm_sub_le (l x • r+K ((A+E) x)) (K (E x))
        have h' := norm_add_le (l x • r) (K ((A+E) x))
        rw [norm_smul] at h'
        linarith
      _ ≤ (‖v-l‖*‖x‖)*‖r‖+B*‖(A+E) x‖+B*(‖E‖*‖x‖) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_right hlx (norm_nonneg _)
          · exact (K.le_opNorm _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
        · exact (K.le_opNorm _).trans (mul_le_mul hK (E.le_opNorm _) (norm_nonneg _) hB)
      _ = _ := by ring
  have hsw := mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
  nlinarith

/-- Apply the original coercivity argument to the actual perturbed inverse
on its kernel complement. It stays valid when the small eigenvalue is zero. -/
theorem moving_stable_inverse_bound (A E K : End ι) (r : Vec ι) (l : Dual ι)
    (hKA : ∀ x,K (A x)=x-l x • r)
    (B : ℝ) (hB : 0≤B) (hK : ‖K‖≤B)
    (d : SimpleSpectralSplit (A+E))
    (hsmall : ‖d.left-l‖*‖r‖+B*‖E‖≤1/2) :
    ‖d.stable‖≤2*B*(1+‖d.projector‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have h := moving_complement_coercivity A E K r l d.left hKA B hB hK hsmall
    (d.stable x) (d.left_stable_zero x)
  rw [d.stable_right] at h
  have hp : ‖x-((d.left d.right)⁻¹*d.left x) • d.right‖≤(1+‖d.projector‖)*‖x‖ := by
    rw [← d.projector_apply]
    have hh := norm_sub_le x (d.projector x)
    have hh' := d.projector.le_opNorm x
    nlinarith
  exact (h.trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans_eq (by ring)

end NonSymmetricDyson.Paper.Spectral
