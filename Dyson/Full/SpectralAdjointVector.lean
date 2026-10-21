import Dyson.Full.SpectralExpansion
import Dyson.Full.SpectralEuclidean

noncomputable section
open scoped BigOperators ComplexConjugate
namespace NonSymmetricDyson.Full.Spectral
open Singularities EuclideanInverse
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def euclideanFunctional (φ : Dual ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  φ.comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).toContinuousLinearMap

def adjointLeftVector (φ : Dual ι) : EuclideanSpace ℂ ι :=
  (InnerProductSpace.toDual ℂ (EuclideanSpace ℂ ι)).symm (euclideanFunctional φ)

@[simp] theorem adjointLeftVector_inner (φ : Dual ι) (x : EuclideanSpace ℂ ι) :
    inner ℂ (adjointLeftVector φ) x = φ (WithLp.ofLp x) := by
  exact InnerProductSpace.toDual_symm_apply

theorem adjointLeftVector_add (φ ψ : Dual ι) :
    adjointLeftVector (φ+ψ)=adjointLeftVector φ+adjointLeftVector ψ := by
  apply ext_inner_right ℂ
  intro x
  simp [inner_add_left]

theorem adjointLeftVector_sub (φ ψ : Dual ι) :
    adjointLeftVector (φ-ψ)=adjointLeftVector φ-adjointLeftVector ψ := by
  apply ext_inner_right ℂ
  intro x
  simp [inner_sub_left]

theorem adjointLeftVector_smul (c : ℂ) (φ : Dual ι) :
    adjointLeftVector (c • φ)=star c • adjointLeftVector φ := by
  apply ext_inner_right ℂ
  intro x
  simp [inner_smul_left]

theorem adjointLeftVector_real (l : ι → ℝ) :
    adjointLeftVector (complexFunctional l)=WithLp.toLp 2 (fun i => (l i:ℂ)) := by
  apply ext_inner_right ℂ
  intro x
  rw [adjointLeftVector_inner]
  simp [PiLp.inner_apply,complexFunctional_apply,RCLike.inner_apply, mul_comm]

theorem adjointLeftVector_comp (φ : Dual ι) (K : End ι) :
    adjointLeftVector (φ.comp K)=(conjugate K).adjoint (adjointLeftVector φ) := by
  apply ext_inner_right ℂ
  intro x
  rw [adjointLeftVector_inner,ContinuousLinearMap.adjoint_inner_left,adjointLeftVector_inner]
  rfl

theorem adjointLeftVector_norm_le (φ : Dual ι) : ‖adjointLeftVector φ‖ ≤ ‖φ‖ := by
  unfold adjointLeftVector
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖φ (WithLp.ofLp x)‖ ≤ ‖φ‖*‖x‖
  exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Norms.sup_le_euclidean (WithLp.ofLp x)) (norm_nonneg _))

/-- The functional estimate is exactly the stated Euclidean adjoint-left
vector expansion. The conjugated real stable inverse has adjoint Kᵀ. -/
theorem adjoint_left_expansion {S : Matrix ι ι ℝ} {m : ι → ℂ}
    {p r l u : ι → ℝ} {K : End ι} {lam δ η ρ C : ℝ}
    (d : SimpleSpectralSplit (SingularSpectral.reducedOperator S m))
    (h : SingularSpectral.HasDysonSpectralEstimates S m p r l u K lam δ η ρ C d) :
    ‖adjointLeftVector d.left - (WithLp.toLp 2 (fun i => (l i:ℂ)) -
      (2*Complex.I*(δ:ℂ)) • (conjugate K).adjoint
        (WithLp.toLp 2 (fun i => ((p i*l i*r i:ℝ):ℂ))))‖ ≤ C*(δ^2+η) := by
  have hh := h.2.2.2.2.2.2.1
  have hb := (adjointLeftVector_norm_le
    (d.left-(complexFunctional l+(2*Complex.I*(δ:ℂ)) •
      (complexFunctional (fun i => p i*l i*r i)).comp K))).trans hh
  rw [adjointLeftVector_sub,adjointLeftVector_add,adjointLeftVector_smul,
    adjointLeftVector_real,adjointLeftVector_comp,adjointLeftVector_real] at hb
  have hc : star (2*Complex.I*(δ:ℂ))= -(2*Complex.I*(δ:ℂ)) := by simp
  simpa only [hc,neg_smul,sub_eq_add_neg] using hb

/-- Supremum-coordinate right-vector errors also imply the paper's ordinary
Euclidean error, with the explicit finite-dimensional conversion constant. -/
theorem right_euclidean_expansion {S : Matrix ι ι ℝ} {m : ι → ℂ}
    {p r l u : ι → ℝ} {K : End ι} {lam δ η ρ C : ℝ}
    (d : SimpleSpectralSplit (SingularSpectral.reducedOperator S m))
    (h : SingularSpectral.HasDysonSpectralEstimates S m p r l u K lam δ η ρ C d) :
    Norms.euclideanNorm (d.right-((fun i => (r i:ℂ)) + (2*Complex.I*(δ:ℂ)) •
      K (fun i => (p i:ℂ)*(r i:ℂ)^2))) ≤
      (Real.sqrt (Fintype.card ι)*C)*(δ^2+η) := by
  have hh := h.2.2.2.2.2.1
  exact (Norms.euclidean_le_sqrt_card_mul_sup _).trans
    ((mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq (by ring))

/-- This is an actual adjoint eigenvector, not merely notation for a dual
estimate. Its eigenvalue is the complex conjugate of the small eigenvalue. -/
theorem adjoint_left_eigen {A : End ι} (d : SimpleSpectralSplit A) :
    (conjugate A).adjoint (adjointLeftVector d.left)=star d.value • adjointLeftVector d.left := by
  have he : d.left.comp A=d.value • d.left := by
    ext x
    exact d.left_eigen x
  rw [← adjointLeftVector_comp,he,adjointLeftVector_smul]

theorem adjoint_left_normalization {A : End ι} (d : SimpleSpectralSplit A)
    (r : ι → ℝ) (h : d.left (fun i => (r i:ℂ))=1) :
    inner ℂ (WithLp.toLp 2 (fun i => (r i:ℂ))) (adjointLeftVector d.left)=1 := by
  have he : inner ℂ (adjointLeftVector d.left) (WithLp.toLp 2 (fun i => (r i:ℂ)))=1 := by
    simpa using h
  rw [← inner_conj_symm,he]
  simp

end NonSymmetricDyson.Full.Spectral
