import Dyson.Full.MainSpectral
import Dyson.Full.SpectralInvertibility
import Dyson.Full.SpectralAdjointVector
import Dyson.Full.CubicUniform

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities Spectral EuclideanInverse
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Exact Euclidean inverse decomposition for the produced spectral split. -/
theorem euclidean_inverse_decomposition {A : End ι} (d : SimpleSpectralSplit A) :
    conjugate d.inverse=d.value⁻¹ • conjugate d.projector+conjugate d.stable := by
  ext x i
  rfl

/-- All inverse and adjoint-complement clauses of the nearby spectral lemma,
with explicit Euclidean constants, follow from the same produced split. -/
theorem spectral_estimates_inverse_consequences
    {S : Matrix ι ι ℝ} {m : ι → ℂ} {p r l u : ι → ℝ} {K : End ι}
    {lam δ η ρ C : ℝ} (hρ : 0<ρ) (hC : 0<C)
    (d : SimpleSpectralSplit (reducedOperator S m))
    (h : HasDysonSpectralEstimates S m p r l u K lam δ η ρ C d) :
    (‖conjugate d.projector‖+
      ‖conjugate (ContinuousLinearMap.id ℂ (Vec ι)-d.projector)‖+
      ‖conjugate d.stable‖+‖(conjugate d.stable).adjoint‖ ≤
      2*Real.sqrt (Fintype.card ι)*C) ∧
    (d.value≠0 →
      (∀ x,conjugate d.inverse (conjugate (reducedOperator S m) x)=x) ∧
      (∀ x,conjugate (reducedOperator S m) (conjugate d.inverse x)=x) ∧
      ‖d.value‖⁻¹ ≤ ‖conjugate d.inverse‖ ∧
      ‖conjugate d.inverse‖ ≤
        (Real.sqrt (Fintype.card ι)*C*(1+ρ/2))*‖d.value‖⁻¹) := by
  have hb := h.2.2.2.2.1
  refine ⟨d.euclidean_stable_bound C hb,?_⟩
  intro hβ
  have hP : ‖d.projector‖≤C := by
    linarith [norm_nonneg (ContinuousLinearMap.id ℂ (Vec ι)-d.projector),norm_nonneg d.stable]
  have hK : ‖d.stable‖≤C := by
    linarith [norm_nonneg d.projector,norm_nonneg (ContinuousLinearMap.id ℂ (Vec ι)-d.projector)]
  exact ⟨d.euclidean_inverse_left hβ,d.euclidean_inverse_right hβ,d.euclidean_inverse_norm_lower,
    by simpa only [div_eq_mul_inv] using (d.euclidean_inverse_norm_upper hβ (ρ/2) C
      (half_pos hρ).le hC.le h.1 hP hK)⟩

/-- At a nonzero real Perron point the produced small eigenvalue is zero;
therefore only the restricted inverse, not the full inverse, is asserted. -/
theorem spectral_value_zero_real_center
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (r : ι → ℝ)
    (hm : ∀ i,m i≠0) (hreal : ∀ i,(m i).im=0) (hr : ∀ i,0<r i)
    (hfixed : saturatedOperator S m (fun i => (r i:ℂ))=(fun i => (r i:ℂ)))
    (d : SimpleSpectralSplit (reducedOperator S m)) : d.value=0 := by
  have hphase : ∀ i,star (m i)/m i=1 := by
    intro i
    have he : star (m i)=m i := by
      apply Complex.ext <;> simp [hreal i]
    rw [he,div_self (hm i)]
  have hkernel : reducedOperator S m (fun i => (r i:ℂ))=0 := by
    ext i
    change (star (m i)/m i)*(r i:ℂ)-saturatedOperator S m (fun i => (r i:ℂ)) i=0
    rw [hphase,hfixed]
    simp
  have hnr : (fun i => (r i:ℂ))≠0 := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := congrFun h i
    have hrne : (r i:ℂ)≠0 := by exact_mod_cast (hr i).ne'
    exact hrne hi
  exact spectral_value_zero_of_kernel d _ hnr hkernel

theorem spectral_projection_idempotent {A : End ι} (d : SimpleSpectralSplit A) (x : Vec ι) :
    d.projector (d.projector x)=d.projector x := by
  calc
    d.projector (d.projector x)=d.projector (((d.left d.right)⁻¹*d.left x) • d.right) :=
      congrArg d.projector (d.projector_apply x)
    _ = ((d.left d.right)⁻¹*d.left x) • d.right := by rw [map_smul,d.projector_right]
    _ = d.projector x := (d.projector_apply x).symm

theorem spectral_projection_commutes {A : End ι} (d : SimpleSpectralSplit A) (x : Vec ι) :
    A (d.projector x)=d.projector (A x) := by
  rw [d.projector_apply,map_smul,d.right_eigen,d.projector_apply,d.left_eigen,smul_smul]
  congr 1
  ring

/-- The stated stable operator really is the inverse on the invariant
kernel of the adjoint-left functional. -/
theorem spectral_complement_inverse {A : End ι} (d : SimpleSpectralSplit A) :
    (∀ x, d.left x=0 → d.left (A x)=0) ∧
    (∀ x, d.left x=0 → d.left (d.stable x)=0 ∧ A (d.stable x)=x) ∧
    (∀ x, d.left x=0 → d.stable (A x)=x) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [d.left_eigen,hx,mul_zero]
  · intro x hx
    exact ⟨d.left_stable_zero x,by simpa [hx] using d.stable_right x⟩
  · intro x hx
    simpa [hx] using d.stable_left x

/-- The sign used in the spectral endpoint is exactly the canonical ratio
used by the uniform σ²+ψ theorem, so those two constructions agree. -/
theorem real_sign_eq_ratio (m : ℂ) (hm : m≠0) (hreal : m.im=0)
    (p : ℝ) (hp : p^2=1) (hpos : 0<p*m.re) : p=m.re/‖m‖ := by
  have he : (m.re:ℂ)=m := by apply Complex.ext <;> simp [hreal]
  have hn : ‖m‖=|m.re| := by rw [← he,Complex.norm_real,Real.norm_eq_abs]; simp
  have hpabs : |p|=1 := by nlinarith [sq_abs p,abs_nonneg p]
  have hnorm : ‖m‖=p*m.re := by
    rw [hn,show |m.re|=|p*m.re| by rw [abs_mul,hpabs,one_mul],abs_of_pos hpos]
  apply (eq_div_iff (norm_ne_zero_iff.mpr hm)).mpr
  rw [hnorm]
  calc
    p*(p*m.re)=p^2*m.re := by ring
    _ = m.re := by rw [hp,one_mul]

theorem stableCoefficient_eq_of_quadratic_image {n : ℕ} [Nonempty (Fin n)]
    (p r u : Fin n → ℝ) (K : End (Fin n))
    (h : K (fun i => (p i:ℂ)*(r i:ℂ)^2)=(fun i => (u i:ℂ))) :
    PerronContinuation.stableCoefficient p r K=u := by
  funext i
  have he := congrArg Complex.re (congrFun h i)
  exact he

end NonSymmetricDyson.Full.SingularSpectral
