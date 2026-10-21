import Dyson.Full.PerronStable
import Dyson.Full.SingularPhysicalInverse

/-! Actual normalized imaginary identities and Taylor coefficients for the
varying small-eigenvalue expansion. These are Dyson algebra, proved here;
the generic simple-eigenvalue perturbation theorem is kept separate. -/

noncomputable section
open scoped Topology BigOperators
open Filter

namespace NonSymmetricDyson.Full.SingularSpectral

open Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def diagonal (d : ι → ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.mul ℂ (ι → ℂ) d

@[simp] theorem diagonal_apply (d x : ι → ℂ) (i : ι) : diagonal d x i = d i*x i := rfl

def firstPhase (p r : ι → ℝ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (-2*Complex.I) • diagonal (fun i => (p i : ℂ)*(r i : ℂ))

def secondPhase (r : ι → ℝ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (-2 : ℂ) • diagonal (fun i => (r i : ℂ)^2)

theorem normalized_imaginary_identity
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    (m i).im/‖m i‖ - ∑ j, (‖m i‖*S i j*‖m j‖)*((m j).im/‖m j‖) = z.im*‖m i‖ := by
  have hq : ∀ j, ‖m j‖ ≠ 0 := fun j => norm_ne_zero_iff.mpr (hm j)
  have he : (∑ j, (‖m i‖*S i j*‖m j‖)*((m j).im/‖m j‖)) =
      ‖m i‖*∑ j, S i j*(m j).im := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hq j]
  rw [he]
  have hh := BasicEstimates.imaginary_part_identity hsol i
  rw [Complex.normSq_eq_norm_sq] at hh
  field_simp [hq i] at hh ⊢
  nlinarith

/-- Applying the actual stable inverse to the exact imaginary equation
produces the varying Perron direction formula, including its η correction. -/
theorem imaginary_direction
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ) (r : ι → ℂ)
    (hF : ∀ x i, F x i = ∑ j, ((‖m i‖*S i j*‖m j‖ : ℝ) : ℂ)*x j)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap ℓ.toLinearMap r) :
    let v : ι → ℂ := fun i => (((m i).im/‖m i‖ : ℝ) : ℂ)
    v = ℓ v • r + (z.im : ℂ) • K (fun i => (‖m i‖ : ℂ)) := by
  intro v
  have hv : v - F v = (z.im : ℂ) • (fun i => (‖m i‖ : ℂ)) := by
    funext i
    simp only [Pi.sub_apply, hF, Pi.smul_apply, smul_eq_mul, v]
    exact_mod_cast normalized_imaginary_identity S a z m hm hsol i
  have hh := hK.left_inverse v
  change K (v - F v) = v - ℓ v • r at hh
  rw [hv, map_smul] at hh
  change (z.im : ℂ) • K (fun i => (‖m i‖ : ℂ)) = v - ℓ v • r at hh
  exact (eq_sub_iff_add_eq.mp hh).symm.trans (add_comm _ _)

theorem firstPhase_right (p r : ι → ℝ) :
    firstPhase p r (fun i => (r i : ℂ)) =
      (-2*Complex.I) • (fun i => (p i : ℂ)*(r i : ℂ)^2) := by
  funext i
  simp only [firstPhase, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    diagonal_apply]
  ring

theorem right_eigenvector_first_coefficient (p r : ι → ℝ)
    (K : (ι → ℂ) →L[ℂ] (ι → ℂ)) :
    -K (firstPhase p r (fun i => (r i : ℂ))) =
      (2*Complex.I) • K (fun i => (p i : ℂ)*(r i : ℂ)^2) := by
  rw [firstPhase_right, map_smul, ← neg_smul]
  congr 1
  ring

theorem eigenvalue_first_coefficient (p r l : ι → ℝ) :
    complexFunctional l (firstPhase p r (fun i => (r i : ℂ))) =
      -2*Complex.I*(quadraticCoefficient p l r : ℂ) := by
  rw [firstPhase_right, map_smul, smul_eq_mul]
  congr 1
  simp only [complexFunctional_apply, quadraticCoefficient, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The second-order scalar coefficient is the manuscript's
2(ψ−σ²), with the stable inverse and its real input explicitly accounted for. -/
theorem eigenvalue_second_coefficient
    (F : ι → ι → ℝ) (p r l u : ι → ℝ)
    (K : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i^2 = 1)
    (hu : ∀ i, u i - ∑ j, F i j*u j = p i*r i^2 - r i*quadraticCoefficient p l r)
    (hKu : K (fun i => (p i : ℂ)*(r i : ℂ)^2) = (fun i => (u i : ℂ))) :
    complexFunctional l (secondPhase r (fun i => (r i : ℂ))) -
      complexFunctional l (firstPhase p r (K (firstPhase p r (fun i => (r i : ℂ))))) =
      (2*(cubicCoefficient F p l r u - (quadraticCoefficient p l r)^2) : ℝ) := by
  rw [firstPhase_right, map_smul, hKu, map_smul, map_smul]
  have halg := cubic_spectral_coefficient_identity F p l r u hp hu
  have he : complexFunctional l (secondPhase r (fun i => (r i : ℂ))) -
      (-2*Complex.I) • complexFunctional l (firstPhase p r (fun i => (u i : ℂ))) =
      ((-2*∑ i, l i*r i^3 + 4*∑ i, p i*l i*r i*u i : ℝ) : ℂ) := by
    simp only [secondPhase, firstPhase, ContinuousLinearMap.smul_apply, map_smul,
      smul_eq_mul, complexFunctional_apply, diagonal_apply, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_ofNat, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h₁ : (∑ i, (l i : ℂ)*((r i : ℂ)^2*(r i : ℂ))) =
        ∑ i, (l i : ℂ)*(r i : ℂ)^3 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h₂ : (∑ i, (l i : ℂ)*((p i : ℂ)*(r i : ℂ)*(u i : ℂ))) =
        ∑ i, (p i : ℂ)*(l i : ℂ)*(r i : ℂ)*(u i : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h₁, h₂]
    ring_nf
    simp [Complex.I_sq]
  rw [he]
  have hr : -2*∑ i, l i*r i^3 + 4*∑ i, p i*l i*r i*u i =
      2*(cubicCoefficient F p l r u - (quadraticCoefficient p l r)^2) := by
    linarith
  exact_mod_cast hr

/-- The linear left functional is the complex conjugate of the manuscript's
adjoint-left vector. Consequently its first correction has sign +2i. -/
theorem left_eigenvector_first_coefficient (p r l : ι → ℝ)
    (K : (ι → ℂ) →L[ℂ] (ι → ℂ)) :
    -(complexFunctional l).comp ((firstPhase p r).comp K) =
      (2*Complex.I) • (complexFunctional (fun i => p i*l i*r i)).comp K := by
  ext x
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, firstPhase, map_smul, smul_eq_mul,
    complexFunctional_apply, diagonal_apply, Complex.ofReal_mul]
  have he : (∑ i, (l i:ℂ)*((p i:ℂ)*(r i:ℂ)*K x i)) =
      ∑ i, (p i:ℂ)*(l i:ℂ)*(r i:ℂ)*K x i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

end NonSymmetricDyson.Full.SingularSpectral
