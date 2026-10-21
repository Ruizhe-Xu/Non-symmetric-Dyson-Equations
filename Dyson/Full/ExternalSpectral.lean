import Mathlib

/-! Universal finite-dimensional simple-eigenvalue perturbation input.
Every object is an arbitrary finite complex operator; no Dyson solution,
phase, density, boundary or model-specific coefficient occurs in this input.
The exact inverse decomposition below is proved internally from the split. -/

noncomputable section
open scoped Topology

namespace NonSymmetricDyson.Full.Spectral

variable {ι : Type*} [Fintype ι]
abbrev Vec (ι : Type*) := ι → ℂ
abbrev End (ι : Type*) [Fintype ι] := Vec ι →L[ℂ] Vec ι
abbrev Dual (ι : Type*) [Fintype ι] := Vec ι →L[ℂ] ℂ

def operatorPolynomial (A : End ι) : Polynomial ℂ := by
  classical
  exact (LinearMap.toMatrix' A.toLinearMap).charpoly

/-- Actual simple eigenvalue, its left and right eigenvectors, and the
inverse on their invariant complement. The left object is the linear
functional represented by the adjoint-left eigenvector in the manuscript. -/
structure SimpleSpectralSplit (A : End ι) where
  value : ℂ
  right : Vec ι
  left : Dual ι
  stable : End ι
  pairing_ne_zero : left right ≠ 0
  right_eigen : A right = value • right
  left_eigen : ∀ x, left (A x) = value*left x
  root : (operatorPolynomial A).eval value = 0
  simple : (operatorPolynomial A).rootMultiplicity value = 1
  stable_right_zero : stable right = 0
  left_stable_zero : ∀ x, left (stable x) = 0
  stable_left : ∀ x, stable (A x) = x - ((left right)⁻¹ * left x) • right
  stable_right : ∀ x, A (stable x) = x - ((left right)⁻¹ * left x) • right

def SimpleSpectralSplit.projector {A : End ι} (d : SimpleSpectralSplit A) : End ι :=
  (d.left d.right)⁻¹ • d.left.smulRight d.right

def SimpleSpectralSplit.inverse {A : End ι} (d : SimpleSpectralSplit A) : End ι :=
  d.value⁻¹ • d.projector + d.stable

/-- Standard quantitative simple spectral perturbation. The base eigenvalue
a is allowed to move near zero. Using the inverse of A on its stable
complement instead of the reduced resolvent at a creates the explicitly
recorded |a| corrections in the Taylor remainders. -/
def SimpleSpectralPerturbationTheory : Prop :=
  ∀ B : ℝ, 0 < B → ∃ ε ρ C : ℝ, 0 < ε ∧ 0 < ρ ∧ 0 < C ∧
    ∀ (A K E : End ι) (r : Vec ι) (ℓ : Dual ι) (a : ℂ),
      ‖r‖ ≤ B → ‖ℓ‖ ≤ B → ‖K‖ ≤ B → ℓ r = 1 →
      A r = a • r → (∀ x, ℓ (A x) = a*ℓ x) →
      K r = 0 → (∀ x, ℓ (K x) = 0) →
      (∀ x, K (A x) = x - ℓ x • r) →
      (∀ x, A (K x) = x - ℓ x • r) → ‖a‖ ≤ ε → ‖E‖ ≤ ε →
      ∃ d : SimpleSpectralSplit (A+E),
        ‖d.value‖ ≤ ρ/2 ∧
        (∀ ζ : ℂ, ‖ζ‖ < ρ → (operatorPolynomial (A+E)).eval ζ = 0 → ζ = d.value) ∧
        ℓ d.right = 1 ∧ d.left r = 1 ∧
        ‖d.projector‖ + ‖(ContinuousLinearMap.id ℂ (Vec ι))-d.projector‖ + ‖d.stable‖ ≤ C ∧
        ‖d.right - (r-K (E r))‖ ≤ C*(‖E‖^2+‖a‖*‖E‖) ∧
        ‖d.left - (ℓ-ℓ.comp (E.comp K))‖ ≤ C*(‖E‖^2+‖a‖*‖E‖) ∧
        ‖d.value - (a+ℓ (E r)-ℓ (E (K (E r))))‖ ≤ C*(‖E‖^3+‖a‖*‖E‖^2)

/-- Equivalent polynomial-input form of quantitative simple spectral perturbation.
The three operators E, E₁, E₂ are arbitrary. This universal Taylor theorem
contains no prescribed phase, Perron or Dyson coefficient. Its small height
parameter permits perturbations whose neglected contribution is O(η). -/
def QuadraticSimpleSpectralPerturbationTheory : Prop :=
  ∀ B : ℝ, 0 < B → ∃ ε ρ C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < ρ ∧ 0 < C ∧
    ∀ (A K E E₁ E₂ : End ι) (r : Vec ι) (ℓ : Dual ι) (a : ℂ) (δ η : ℝ),
      ‖r‖ ≤ B → ‖ℓ‖ ≤ B → ‖K‖ ≤ B → ‖E₁‖ ≤ B → ‖E₂‖ ≤ B →
      ℓ r = 1 → A r = a • r → (∀ x, ℓ (A x) = a*ℓ x) →
      K r = 0 → (∀ x, ℓ (K x) = 0) →
      (∀ x, K (A x) = x - ℓ x • r) →
      (∀ x, A (K x) = x - ℓ x • r) →
      0 ≤ δ → δ ≤ ε → 0 ≤ η → η ≤ ε → ‖a‖ ≤ ε →
      ‖a‖*δ ≤ B*η → ‖E‖ ≤ B*δ →
      ‖E - (δ:ℂ) • E₁ - ((δ:ℂ)^2) • E₂‖ ≤ B*(δ^3+η) →
      ∃ d : SimpleSpectralSplit (A+E),
        ‖d.value‖ ≤ ρ/2 ∧
        (∀ ζ : ℂ, ‖ζ‖ < ρ → (operatorPolynomial (A+E)).eval ζ = 0 → ζ = d.value) ∧
        ℓ d.right = 1 ∧ d.left r = 1 ∧
        ‖d.projector‖ + ‖(ContinuousLinearMap.id ℂ (Vec ι))-d.projector‖ + ‖d.stable‖ ≤ C ∧
        ‖d.right - (r-(δ:ℂ) • K (E₁ r))‖ ≤ C*(δ^2+η) ∧
        ‖d.left - (ℓ-(δ:ℂ) • ℓ.comp (E₁.comp K))‖ ≤ C*(δ^2+η) ∧
        ‖d.value - (a+(δ:ℂ)*ℓ (E₁ r)+(δ:ℂ)^2*(ℓ (E₂ r)-ℓ (E₁ (K (E₁ r)))))‖ ≤
          C*(δ^3+η)

namespace SimpleSpectralSplit

variable {A : End ι} (d : SimpleSpectralSplit A)

@[simp] theorem projector_apply (x : Vec ι) :
    d.projector x = ((d.left d.right)⁻¹*d.left x) • d.right := by
  simp [SimpleSpectralSplit.projector, smul_smul]

@[simp] theorem projector_right : d.projector d.right = d.right := by
  simp [projector_apply, d.pairing_ne_zero]

theorem right_ne_zero : d.right ≠ 0 := by
  intro h
  exact d.pairing_ne_zero (by simp [h])

theorem inverse_left (hβ : d.value ≠ 0) (x : Vec ι) : d.inverse (A x) = x := by
  simp only [inverse, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    projector_apply, d.left_eigen, d.stable_left, smul_smul]
  have hc : d.value⁻¹ * ((d.left d.right)⁻¹ * (d.value*d.left x)) =
      (d.left d.right)⁻¹*d.left x := by field_simp
  rw [hc]
  abel

theorem inverse_right (hβ : d.value ≠ 0) (x : Vec ι) : A (d.inverse x) = x := by
  simp only [inverse, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, projector_apply, d.right_eigen, d.stable_right, smul_smul]
  have hc : (d.value⁻¹ * ((d.left d.right)⁻¹*d.left x))*d.value =
      (d.left d.right)⁻¹*d.left x := by field_simp
  rw [hc]
  abel

theorem inverse_apply_right : d.inverse d.right = d.value⁻¹ • d.right := by
  simp [inverse, d.stable_right_zero, d.pairing_ne_zero]

theorem inverse_norm_upper : ‖d.inverse‖ ≤ ‖d.value‖⁻¹*‖d.projector‖+‖d.stable‖ := by
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_inv])

theorem inverse_norm_lower : ‖d.value‖⁻¹ ≤ ‖d.inverse‖ := by
  have hh := d.inverse.le_opNorm d.right
  rw [d.inverse_apply_right, norm_smul, norm_inv] at hh
  exact le_of_mul_le_mul_right hh (norm_pos_iff.mpr d.right_ne_zero)

end SimpleSpectralSplit
end NonSymmetricDyson.Full.Spectral
