import Dyson.Full.ExternalSpectral
import Dyson.Full.SpectralPhase

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities Spectral
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def reducedOperator (S : Matrix ι ι ℝ) (m : ι → ℂ) : End ι :=
  phaseOperator m-saturatedOperator S m

theorem stable_coefficient_equation (F : Matrix ι ι ℝ) (p r l u : ι → ℝ)
    (K : End ι)
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ)))
    (hKu : K (fun i => (p i:ℂ)*(r i:ℂ)^2) = fun i => (u i:ℂ)) :
    ∀ i, u i-∑ j, F i j*u j = p i*r i^2-r i*quadraticCoefficient p l r := by
  have hh := hK.right_inverse (fun i => (p i:ℂ)*(r i:ℂ)^2)
  change K _ - complexMatrixOperator F (K _) = _ at hh
  rw [hKu] at hh
  have hs : complexFunctional l (fun i => (p i:ℂ)*(r i:ℂ)^2) =
      (quadraticCoefficient p l r:ℂ) := by
    simp only [complexFunctional_apply, quadraticCoefficient, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change ((fun i => (u i:ℂ))-complexMatrixOperator F (fun i => (u i:ℂ))) =
    (fun i => (p i:ℂ)*(r i:ℂ)^2)-
      complexFunctional l (fun i => (p i:ℂ)*(r i:ℂ)^2) • (fun i => (r i:ℂ)) at hh
  rw [hs] at hh
  intro i
  have hi := congrFun hh i
  simp only [Pi.sub_apply, complexMatrixOperator_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hr : (u i:ℂ)-∑ j, (F i j:ℂ)*(u j:ℂ) =
      (p i:ℂ)*(r i:ℂ)^2-(r i:ℂ)*(quadraticCoefficient p l r:ℂ) := by
    simpa [mul_comm] using hi
  exact_mod_cast hr

/-- The manuscript's varying eigenvalue, right vector and adjoint-left vector
Taylor estimates, stated using the equivalent linear left functional. All
coefficients contain the actual saturated matrix and restricted inverse. -/
def HasDysonSpectralEstimates (S : Matrix ι ι ℝ) (m : ι → ℂ)
    (p r l u : ι → ℝ) (K : End ι) (lam δ η ρ C : ℝ)
    (d : SimpleSpectralSplit (reducedOperator S m)) : Prop :=
  ‖d.value‖ ≤ ρ/2 ∧
  (∀ ζ : ℂ, ‖ζ‖ < ρ → (operatorPolynomial (reducedOperator S m)).eval ζ = 0 → ζ=d.value) ∧
  complexFunctional l d.right = 1 ∧ d.left (fun i => (r i:ℂ)) = 1 ∧
  ‖d.projector‖ + ‖ContinuousLinearMap.id ℂ (Vec ι)-d.projector‖ + ‖d.stable‖ ≤ C ∧
  ‖d.right - ((fun i => (r i:ℂ)) + (2*Complex.I*(δ:ℂ)) •
    K (fun i => (p i:ℂ)*(r i:ℂ)^2))‖ ≤ C*(δ^2+η) ∧
  ‖d.left - (complexFunctional l + (2*Complex.I*(δ:ℂ)) •
    (complexFunctional (fun i => p i*l i*r i)).comp K)‖ ≤ C*(δ^2+η) ∧
  ‖d.value - ((1-lam:ℝ):ℂ) + 2*Complex.I*(quadraticCoefficient p l r:ℂ)*(δ:ℂ) -
    2*((cubicCoefficient (fun i j => ‖m i‖*S i j*‖m j‖) p l r u-
      (quadraticCoefficient p l r)^2:ℝ):ℂ)*(δ:ℂ)^2‖ ≤ C*(δ^3+η)

/-- Universal spectral perturbation applied to the actual Dyson phase. The
input inequalities are uniform boundedness/smallness conditions, while the
spectral split, unique simple small eigenvalue and all three manuscript Taylor
coefficients are conclusions. -/
theorem dyson_spectral_expansion
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := ι))
    (B : ℝ) (hB : 0 < B) :
    ∃ ε ρ C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < ρ ∧ 0 < C ∧
    ∀ (S : Matrix ι ι ℝ) (m : ι → ℂ) (p r l u : ι → ℝ) (K : End ι)
      (lam δ η : ℝ),
      ‖(fun i => (r i:ℂ))‖ ≤ B → ‖complexFunctional l‖ ≤ B → ‖K‖ ≤ B →
      ‖firstPhase p r‖ ≤ B → ‖secondPhase r‖ ≤ B →
      complexFunctional l (fun i => (r i:ℂ)) = 1 →
      saturatedOperator S m (fun i => (r i:ℂ)) = (lam:ℂ) • (fun i => (r i:ℂ)) →
      (∀ x, complexFunctional l (saturatedOperator S m x) = (lam:ℂ)*complexFunctional l x) →
      IsRestrictedInverse (saturatedOperator S m).toLinearMap K.toLinearMap
        (complexFunctional l).toLinearMap (fun i => (r i:ℂ)) →
      (∀ i, p i^2=1) →
      K (fun i => (p i:ℂ)*(r i:ℂ)^2) = (fun i => (u i:ℂ)) →
      0 ≤ δ → δ ≤ ε → 0 ≤ η → η ≤ ε → |1-lam| ≤ ε →
      |1-lam| * δ ≤ B*η →
      ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι)‖ ≤ B*δ →
      ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι) -
        (δ:ℂ) • firstPhase p r - ((δ:ℂ)^2) • secondPhase r‖ ≤ B*(δ^3+η) →
      ∃ d : SimpleSpectralSplit (reducedOperator S m),
        HasDysonSpectralEstimates S m p r l u K lam δ η ρ C d := by
  obtain ⟨ε,ρ,C,hε,hε1,hρ,hC,ht⟩ := external B hB
  refine ⟨ε,ρ,C,hε,hε1,hρ,hC,?_⟩
  intro S m p r l u K lam δ η hr hl hKb hE1 hE2 hnorm hright hleft hK hp hKu
    hδ hδε hη hηε ha hprod hE hrem
  let A : End ι := ContinuousLinearMap.id ℂ (Vec ι)-saturatedOperator S m
  let E : End ι := phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι)
  have hAr : A (fun i => (r i:ℂ)) = ((1-lam:ℝ):ℂ) • (fun i => (r i:ℂ)) := by
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hright]
    simp [sub_smul]
  have hAl : ∀ x, complexFunctional l (A x) = ((1-lam:ℝ):ℂ)*complexFunctional l x := by
    intro x
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hleft]
    push_cast
    ring
  have hKA : ∀ x, K (A x)=x-complexFunctional l x • (fun i => (r i:ℂ)) := hK.left_inverse
  have hAK : ∀ x, A (K x)=x-complexFunctional l x • (fun i => (r i:ℂ)) := hK.right_inverse
  have ha' : ‖((1-lam:ℝ):ℂ)‖ ≤ ε := by simpa only [Complex.norm_real, Real.norm_eq_abs] using ha
  have hp' : ‖((1-lam:ℝ):ℂ)‖*δ ≤ B*η := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hprod
  have hh := ht A K E (firstPhase p r) (secondPhase r)
    (fun i => (r i:ℂ)) (complexFunctional l) ((1-lam:ℝ):ℂ) δ η
    hr hl hKb hE1 hE2 hnorm hAr hAl hK.kill_right hK.kill_left hKA hAK
    hδ hδε hη hηε ha' hp' hE hrem
  have heq : A+E = reducedOperator S m := by dsimp [A,E,reducedOperator]; abel
  rw [heq] at hh
  obtain ⟨d,hd⟩ := hh
  obtain ⟨hv,hunique,hnr,hnl,hbound,hvr,hvl,hbeta⟩ := hd
  refine ⟨d,hv,hunique,hnr,hnl,hbound,?_,?_,?_⟩
  · have he : (fun i => (r i:ℂ)) - (δ:ℂ) • K (firstPhase p r (fun i => (r i:ℂ))) =
        (fun i => (r i:ℂ)) + (2*Complex.I*(δ:ℂ)) • K (fun i => (p i:ℂ)*(r i:ℂ)^2) := by
      rw [sub_eq_add_neg, ← smul_neg, right_eigenvector_first_coefficient, smul_smul]
      congr 2
      ring
    simpa only [he] using hvr
  · have he : complexFunctional l-(δ:ℂ) • (complexFunctional l).comp ((firstPhase p r).comp K) =
        complexFunctional l+(2*Complex.I*(δ:ℂ)) •
          (complexFunctional (fun i => p i*l i*r i)).comp K := by
      calc
        _ = complexFunctional l + (δ:ℂ) •
            (-(complexFunctional l).comp ((firstPhase p r).comp K)) := by module
        _ = complexFunctional l + (δ:ℂ) • ((2*Complex.I) •
            (complexFunctional (fun i => p i*l i*r i)).comp K) := by
          rw [left_eigenvector_first_coefficient]
        _ = _ := by rw [smul_smul]; congr 2; ring
    simpa only [he] using hvl
  · have hu := stable_coefficient_equation _ p r l u K hK hKu
    rw [eigenvalue_first_coefficient,
      eigenvalue_second_coefficient _ p r l u K hp hu hKu] at hbeta
    convert hbeta using 1 <;> congr 1 <;> push_cast <;> ring

end NonSymmetricDyson.Full.SingularSpectral
