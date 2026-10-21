import Dyson.Paper.SpectralResidual
import Dyson.Paper.SpectralLengths

/-! Exact clauses of the revised local spectral lemma, with boundary
conventions and actual Euclidean adjoint-left vector. This is output data
constructed from proved phase/coefficient identities and general spectral theory. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Spectral Full.Singularities Full.SingularSpectral Full.PerronContinuation
variable {n : ℕ} [Nonempty (Fin n)]

structure ExpansionAt (S : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℂ)
    (p r l : Fin n → ℝ) (K : End (Fin n)) (lam eta rho C CU b B : ℝ) where
  u : Fin n → ℝ
  split : SimpleSpectralSplit (reducedOperator S m)
  stable_coefficient : K (fun i => (p i:ℂ)*(r i:ℂ)^2)=fun i => (u i:ℂ)
  estimates : HasDysonSpectralEstimates S m p r l u K lam (perronDensity l m) eta rho C split
  phase_remainder : ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec (Fin n))-
    (perronDensity l m:ℂ) • firstPhase p r-((perronDensity l m:ℂ)^2) • secondPhase r‖≤
    CU*((perronDensity l m)^3+eta)
  gap : ∀ z : ℂ,(operatorPolynomial (reducedOperator S m)).eval z=0 → z≠split.value →
    rho/2≤‖z‖-‖split.value‖
  right_lengths : ∀ i,b≤‖split.right i‖ ∧ ‖split.right i‖≤B
  left_lengths : ∀ i,b≤‖adjointLeftVector split.left i‖ ∧ ‖adjointLeftVector split.left i‖≤B
  pairing_lengths : b≤‖split.left split.right‖ ∧ ‖split.left split.right‖≤B
  ratio_positive_denominator : 0 < mu l m
  ratio_identity : mu l m*extendedHeightRatio lam l m=1-lam
  scalar_expansion : ‖split.value-((mu l m*extendedHeightRatio lam l m:ℝ):ℂ)+
    2*Complex.I*(quadraticCoefficient p l r:ℂ)*(perronDensity l m:ℂ)-
    2*((cubicCoefficient (saturatedMatrix S m) p l r u-(quadraticCoefficient p l r)^2:ℝ):ℂ)*
      (perronDensity l m:ℂ)^2‖≤C*((perronDensity l m)^3+eta)
  schur : ∀ z : ℂ,∀ J : ComplementResolvent (reducedOperator S m)
    (fun i => (r i:ℂ)) (complexFunctional l) z,
    (∃ x : Vec (Fin n),x≠0 ∧ reducedOperator S m x=z • x) ↔
      schurScalar (reducedOperator S m) (fun i => (r i:ℂ)) (complexFunctional l) z J=0
  right_residual : let E := phaseOperator m-ContinuousLinearMap.id ℂ (Vec (Fin n))
    let w := split.right-(fun i => (r i:ℂ))
    complexFunctional l w=0 ∧
    w= -K (E (fun i => (r i:ℂ)))-K (E w)+split.value • K w ∧
    split.value=((1-lam:ℝ):ℂ)+complexFunctional l (E (fun i => (r i:ℂ)))+complexFunctional l (E w)
  stable_bound : ‖EuclideanInverse.conjugate split.projector‖+
    ‖EuclideanInverse.conjugate (ContinuousLinearMap.id ℂ (Vec (Fin n))-split.projector)‖+
    ‖EuclideanInverse.conjugate split.stable‖+‖(EuclideanInverse.conjugate split.stable).adjoint‖≤
    2*Real.sqrt n*C
  inverse_bound : split.value≠0 →
    (∀ x,EuclideanInverse.conjugate split.inverse (EuclideanInverse.conjugate (reducedOperator S m) x)=x) ∧
    (∀ x,EuclideanInverse.conjugate (reducedOperator S m) (EuclideanInverse.conjugate split.inverse x)=x) ∧
    ‖split.value‖⁻¹≤‖EuclideanInverse.conjugate split.inverse‖ ∧
    ‖EuclideanInverse.conjugate split.inverse‖≤(Real.sqrt n*C*(1+rho/2))*‖split.value‖⁻¹

/-- Assembly is internal: all source-specific interpretations, coefficient
identities, gap and inverse consequences are attached to the same split. -/
theorem expansionAt_of_estimates
    (S : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℂ)
    (p r l u : Fin n → ℝ) (K : End (Fin n)) (lam eta rho C CU b B : ℝ)
    (hm : ∀ i,m i≠0) (hd : PerronData (saturatedMatrix S m) lam r l)
    (hK : IsRestrictedInverse (saturatedOperator S m).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ)))
    (hrho : 0<rho) (hC : 0<C)
    (d : SimpleSpectralSplit (reducedOperator S m))
    (hu : K (fun i => (p i:ℂ)*(r i:ℂ)^2)=fun i => (u i:ℂ))
    (hest : HasDysonSpectralEstimates S m p r l u K lam (perronDensity l m) eta rho C d)
    (hphase : ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec (Fin n))-
      (perronDensity l m:ℂ) • firstPhase p r-((perronDensity l m:ℂ)^2) • secondPhase r‖≤
      CU*((perronDensity l m)^3+eta))
    (hrlen : ∀ i,b≤‖d.right i‖ ∧ ‖d.right i‖≤B)
    (hllen : ∀ i,b≤‖leftCoefficient d.left i‖ ∧ ‖leftCoefficient d.left i‖≤B)
    (hpair : b≤‖d.left d.right‖ ∧ ‖d.left d.right‖≤B) :
    Nonempty (ExpansionAt S m p r l K lam eta rho C CU b B) := by
  have hnorm : complexFunctional l (fun i => (r i:ℂ))=1 := by
    rw [complexFunctional_apply]
    exact_mod_cast hd.normalized
  have hr : saturatedOperator S m (fun i => (r i:ℂ))=(lam:ℂ) • (fun i => (r i:ℂ)) := by
    ext i
    change (∑ j,((saturatedMatrix S m i j:ℝ):ℂ)*(r j:ℂ))=(lam:ℂ)*(r i:ℂ)
    exact_mod_cast hd.right_eigen i
  have hl : ∀ x,complexFunctional l (saturatedOperator S m x)=(lam:ℂ)*complexFunctional l x :=
    functional_left_eigen_general _ l lam hd.left_eigen
  have hmu := mu_positive l m hd.left_positive hm
  have hratio : mu l m*extendedHeightRatio lam l m=1-lam := by
    unfold extendedHeightRatio
    field_simp [hmu.ne']
  obtain ⟨hstable,hinv⟩ := spectral_estimates_inverse_consequences hrho hC d hest
  refine ⟨{
    u := u
    split := d
    stable_coefficient := hu
    estimates := hest
    phase_remainder := hphase
    gap := ?_
    right_lengths := hrlen
    left_lengths := ?_
    pairing_lengths := hpair
    ratio_positive_denominator := hmu
    ratio_identity := hratio
    scalar_expansion := ?_
    schur := fun z J => eigenvalue_iff_schur_zero _ _ _ hnorm z J
    right_residual := dyson_spectral_residual S m r l lam K hnorm hr hl hK d hest.2.2.1
    stable_bound := by simpa only [Fintype.card_fin] using hstable
    inverse_bound := by simpa only [Fintype.card_fin] using hinv }⟩
  · intro z hz hne
    have hrz : rho≤‖z‖ := le_of_not_gt (fun hh => hne (hest.2.1 z hh hz))
    linarith [hest.1]
  · intro i
    rw [adjointLeftVector_coordinate_norm]
    exact hllen i
  · rw [hratio]
    exact hest.2.2.2.2.2.2.2

namespace ExpansionAt
variable {S : Matrix (Fin n) (Fin n) ℝ} {m : Fin n → ℂ}
  {p r l : Fin n → ℝ} {K : End (Fin n)} {lam eta rho C CU b B : ℝ}
  (data : ExpansionAt S m p r l K lam eta rho C CU b B)

theorem adjoint_eigen :
    (EuclideanInverse.conjugate (reducedOperator S m)).adjoint (adjointLeftVector data.split.left)=
      star data.split.value • adjointLeftVector data.split.left := adjoint_left_eigen data.split

theorem left_normalization : inner ℂ (WithLp.toLp 2 (fun i => (r i:ℂ)))
    (adjointLeftVector data.split.left)=1 :=
  adjoint_left_normalization data.split r data.estimates.2.2.2.1

theorem left_expansion :
    ‖adjointLeftVector data.split.left-(WithLp.toLp 2 (fun i => (l i:ℂ))-
      (2*Complex.I*(perronDensity l m:ℂ)) • (EuclideanInverse.conjugate K).adjoint
        (WithLp.toLp 2 (fun i => ((p i*l i*r i:ℝ):ℂ))))‖≤C*((perronDensity l m)^2+eta) :=
  adjoint_left_expansion data.split data.estimates

theorem right_expansion :
    Norms.euclideanNorm (data.split.right-((fun i => (r i:ℂ))+
      (2*Complex.I*(perronDensity l m:ℂ)) • K (fun i => (p i:ℂ)*(r i:ℂ)^2)))≤
      (Real.sqrt n*C)*((perronDensity l m)^2+eta) := by
  simpa only [Fintype.card_fin] using right_euclidean_expansion data.split data.estimates

theorem restricted_inverse :
    (∀ x,data.split.left x=0 → data.split.left (reducedOperator S m x)=0) ∧
    (∀ x,data.split.left x=0 → data.split.left (data.split.stable x)=0 ∧
      reducedOperator S m (data.split.stable x)=x) ∧
    (∀ x,data.split.left x=0 → data.split.stable (reducedOperator S m x)=x) :=
  spectral_complement_inverse data.split

theorem inverse_decomposition :
    EuclideanInverse.conjugate data.split.inverse=
      data.split.value⁻¹ • EuclideanInverse.conjugate data.split.projector+
      EuclideanInverse.conjugate data.split.stable := euclidean_inverse_decomposition data.split

end ExpansionAt

end NonSymmetricDyson.Paper.Spectral
