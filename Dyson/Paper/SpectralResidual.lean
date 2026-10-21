import Dyson.Paper.SpectralSchur
import Dyson.Full.SpectralExpansion

/-! Exact original Step 2 block cancellation and Step 3 eigenvector/scalar
identities. The small-eigenvalue existence is separate generic spectral theory;
none of these Dyson coefficient or residual identities is assumed. -/
noncomputable section
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Spectral Full.Singularities Full.SingularSpectral
variable {ι : Type*} [Fintype ι]

/-- The original block cancellation: only E couples the Perron line to its
complement, and the scalar block equals a+l(E r). -/
theorem adapted_block_cancellation (A E : End ι) (r : Vec ι) (l : Dual ι) (a : ℂ)
    (hnorm : l r=1) (hr : A r=a • r) (hl : ∀ x,l (A x)=a*l x) :
    l ((A+E) r)=a+l (E r) ∧
    complement r l ((A+E) r)=complement r l (E r) ∧
    (∀ y,l y=0 → l ((A+E) y)=l (E y)) := by
  refine ⟨?_,?_,?_⟩
  · simp [hr,hnorm]
  · simp [hr,complement_apply,hnorm,add_smul]
  · intro y hy
    simp [hl,hy]

/-- The source's exact w equation after applying the stable inverse. -/
theorem right_eigenvector_residual (A E K : End ι) (r t : Vec ι)
    (l : Dual ι) (a beta : ℂ)
    (hnorm : l r=1) (htnorm : l t=1)
    (hr : A r=a • r) (hKr : K r=0)
    (hKA : ∀ x,K (A x)=x-l x • r)
    (ht : (A+E) t=beta • t) :
    l (t-r)=0 ∧ t-r= -K (E r)-K (E (t-r))+beta • K (t-r) := by
  have hw : l (t-r)=0 := by simp [htnorm,hnorm]
  refine ⟨hw,?_⟩
  have hh := congrArg K ht
  simp only [ContinuousLinearMap.add_apply,map_add,map_smul,hKA,htnorm,one_smul] at hh
  have hk : K (t-r)=K t := by simp [hKr]
  rw [hk]
  have hE : K (E t)=K (E r)+K (E (t-r)) := by
    rw [map_sub,map_sub]
    abel
  rw [hE] at hh
  linear_combination hh

/-- Applying l to the actual right eigenvector equation gives the scalar
identity used to calculate both σ and ψ, without an expansion assumption. -/
theorem eigenvalue_scalar_identity (A E : End ι) (r t : Vec ι)
    (l : Dual ι) (a beta : ℂ)
    (hnorm : l r=1) (htnorm : l t=1)
    (hl : ∀ x,l (A x)=a*l x)
    (ht : (A+E) t=beta • t) :
    beta=a+l (E r)+l (E (t-r)) := by
  have hh := congrArg l ht
  simp only [ContinuousLinearMap.add_apply,map_add,map_smul,smul_eq_mul,hl,htnorm,mul_one] at hh
  rw [map_sub,map_sub]
  linear_combination -hh

/-- The original a priori absorption, with an explicit factor 2. -/
theorem right_residual_absorption (E K : End ι) (r w : Vec ι) (beta : ℂ)
    (heq : w= -K (E r)-K (E w)+beta • K w)
    (B : ℝ) (hB : 0≤B) (hK : ‖K‖≤B)
    (hsmall : B*(‖E‖+‖beta‖)≤1/2) :
    ‖w‖≤2*B*‖E‖*‖r‖ := by
  have hb : ‖w‖≤B*‖E‖*‖r‖+B*(‖E‖+‖beta‖)*‖w‖ := by
    calc
      ‖w‖ = ‖-K (E r)-K (E w)+beta • K w‖ := congrArg norm heq
      _ ≤ ‖K (E r)‖+‖K (E w)‖+‖beta‖*‖K w‖ := by
        have h := norm_add_le (-K (E r)-K (E w)) (beta • K w)
        have h' := norm_sub_le (-K (E r)) (K (E w))
        rw [norm_neg] at h'
        rw [norm_smul] at h
        linarith
      _ ≤ B*(‖E‖*‖r‖)+B*(‖E‖*‖w‖)+‖beta‖*(B*‖w‖) := by
        gcongr
        · exact (K.le_opNorm _).trans (mul_le_mul hK (E.le_opNorm _) (norm_nonneg _) hB)
        · exact (K.le_opNorm _).trans (mul_le_mul hK (E.le_opNorm _) (norm_nonneg _) hB)
        · exact (K.le_opNorm _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
      _ = _ := by ring
  have hsmallw := mul_le_mul_of_nonneg_right hsmall (norm_nonneg w)
  nlinarith

/-- Actual Dyson specialization of the two exact Step 3 identities. -/
theorem dyson_spectral_residual [Nonempty ι]
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (r l : ι → ℝ) (lam : ℝ)
    (K : End ι)
    (hnorm : complexFunctional l (fun i => (r i:ℂ))=1)
    (hr : saturatedOperator S m (fun i => (r i:ℂ))=(lam:ℂ) • (fun i => (r i:ℂ)))
    (hl : ∀ x,complexFunctional l (saturatedOperator S m x)=(lam:ℂ)*complexFunctional l x)
    (hK : IsRestrictedInverse (saturatedOperator S m).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ)))
    (d : SimpleSpectralSplit (reducedOperator S m))
    (hdt : complexFunctional l d.right=1) :
    let E := phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι)
    let w := d.right-(fun i => (r i:ℂ))
    complexFunctional l w=0 ∧
    w= -K (E (fun i => (r i:ℂ)))-K (E w)+d.value • K w ∧
    d.value=((1-lam:ℝ):ℂ)+complexFunctional l (E (fun i => (r i:ℂ)))+
      complexFunctional l (E w) := by
  intro E w
  let A := ContinuousLinearMap.id ℂ (Vec ι)-saturatedOperator S m
  have hAe : A+E=reducedOperator S m := by dsimp [A,E,reducedOperator]; abel
  have hAr : A (fun i => (r i:ℂ))=((1-lam:ℝ):ℂ) • (fun i => (r i:ℂ)) := by
    simp only [A,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,hr,Complex.ofReal_sub,
      Complex.ofReal_one,sub_smul,one_smul]
  have hAl : ∀ x,complexFunctional l (A x)=((1-lam:ℝ):ℂ)*complexFunctional l x := by
    intro x
    change complexFunctional l (x-saturatedOperator S m x)=_
    rw [map_sub,hl]
    push_cast
    ring
  have hKA : ∀ x,K (A x)=x-complexFunctional l x • (fun i => (r i:ℂ)) := hK.left_inverse
  have ht : (A+E) d.right=d.value • d.right := by rw [hAe]; exact d.right_eigen
  obtain ⟨hw,he⟩ := right_eigenvector_residual A E K _ d.right (complexFunctional l)
    ((1-lam:ℝ):ℂ) d.value hnorm hdt hAr hK.kill_right hKA ht
  exact ⟨hw,he,eigenvalue_scalar_identity A E _ d.right (complexFunctional l)
    ((1-lam:ℝ):ℂ) d.value hnorm hdt hAl ht⟩

end NonSymmetricDyson.Paper.Spectral
