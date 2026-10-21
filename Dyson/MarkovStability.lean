import Dyson.Model
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A quantitative phase--Markov stability bound

For a nonnegative row-stochastic finite matrix Q and phases U with |Uᵢ|=1,
the operator U - lam Q satisfies (1-lam) ||w||∞ ≤ ||(U-lamQ)w||∞ for lam≥0.
The Markov contraction is proved from the actual matrix entries. This is the
interior-gap term of the manuscript's graph-resonance stability inequality;
the additional graph phase-defect term is not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.MarkovStability

variable {ι : Type*} [Fintype ι]

/-- Entrywise multiplication by a family of unit complex phases. -/
def phaseMultiply (U w : ι → ℂ) : ι → ℂ := fun i => U i * w i

/-- Multiplication by unit phases preserves the complex supremum norm. -/
theorem phaseMultiply_norm (U w : ι → ℂ) (hU : ∀ i, ‖U i‖ = 1) :
    ‖phaseMultiply U w‖ = ‖w‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
    intro i
    simpa [phaseMultiply, norm_mul, hU i] using norm_le_pi_norm w i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (phaseMultiply U w))).mpr
    intro i
    have hi := norm_le_pi_norm (phaseMultiply U w) i
    simpa [phaseMultiply, norm_mul, hU i] using hi

/-- A nonnegative row-stochastic matrix contracts the finite supremum norm. -/
theorem markov_norm_contraction (Q : Matrix ι ι ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (w : ι → ℂ) : ‖Model.action Q w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  calc
    ‖Model.action Q w i‖ = ‖∑ j, (Q i j : ℂ) * w j‖ := rfl
    _ ≤ ∑ j, ‖(Q i j : ℂ) * w j‖ := norm_sum_le _ _
    _ = ∑ j, Q i j * ‖w j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ i j)]
    _ ≤ ∑ j, Q i j * ‖w‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm w j) (hQ i j)
    _ = ‖w‖ := by rw [← Finset.sum_mul, hrow i, one_mul]

/-- The actual complex-linear phase--Markov operator `diag(U) - lam Q`. -/
def phaseMarkovOperator (Q : Matrix ι ι ℝ) (U : ι → ℂ) (lam : ℝ) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun w := phaseMultiply U w - (lam : ℂ) • Model.action Q w
  map_add' w v := by
    ext i
    simp only [phaseMultiply, map_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  map_smul' c w := by
    ext i
    simp only [phaseMultiply, map_smul, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem phaseMarkovOperator_apply (Q : Matrix ι ι ℝ)
    (U w : ι → ℂ) (lam : ℝ) (i : ι) :
    phaseMarkovOperator Q U lam w i =
      U i * w i - (lam : ℂ) * ∑ j, (Q i j : ℂ) * w j := rfl

/-- The interior-gap lower bound in the manuscript's phase--Markov stability
estimate. The inequality holds for every lam≥0, in particular for 0≤lam≤1. -/
theorem phase_markov_lower_bound (Q : Matrix ι ι ℝ) (U : ι → ℂ) (lam : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (hU : ∀ i, ‖U i‖ = 1) (hlam : 0 ≤ lam) (w : ι → ℂ) :
    (1 - lam) * ‖w‖ ≤ ‖phaseMarkovOperator Q U lam w‖ := by
  have hmarkov := markov_norm_contraction Q hQ hrow w
  have hnorm : ‖(lam : ℂ) • Model.action Q w‖ ≤ lam * ‖w‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left hmarkov hlam
  have htriangle := norm_sub_norm_le (phaseMultiply U w) ((lam : ℂ) • Model.action Q w)
  rw [phaseMultiply_norm U w hU] at htriangle
  change (1 - lam) * ‖w‖ ≤ ‖phaseMultiply U w - (lam : ℂ) • Model.action Q w‖
  nlinarith

/-- The operator has trivial kernel when the Markov parameter lies in [0,1). -/
theorem phase_markov_kernel_trivial (Q : Matrix ι ι ℝ) (U : ι → ℂ) (lam : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (hU : ∀ i, ‖U i‖ = 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {w : ι → ℂ} (hw : phaseMarkovOperator Q U lam w = 0) : w = 0 := by
  have hbound := phase_markov_lower_bound Q U lam hQ hrow hU hlam0 w
  rw [hw, norm_zero] at hbound
  have hn : ‖w‖ = 0 := le_antisymm
    (by nlinarith [norm_nonneg w]) (norm_nonneg w)
  exact norm_eq_zero.mp hn

/-- The finite-dimensional phase--Markov operator is invertible for lam∈[0,1). -/
theorem phase_markov_bijective (Q : Matrix ι ι ℝ) (U : ι → ℂ) (lam : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (hU : ∀ i, ‖U i‖ = 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) :
    Function.Bijective (phaseMarkovOperator Q U lam) := by
  have hinj : Function.Injective (phaseMarkovOperator Q U lam) := by
    intro w v hwv
    have hz : phaseMarkovOperator Q U lam (w - v) = 0 := by rw [map_sub, hwv, sub_self]
    exact sub_eq_zero.mp (phase_markov_kernel_trivial Q U lam hQ hrow hU hlam0 hlam1 hz)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The quantitative inverse bound `||w||∞ ≤ (1-lam)⁻¹ ||v||∞`
for an actual solution of `(U - lam Q) w = v`. -/
theorem phase_markov_inverse_bound (Q : Matrix ι ι ℝ) (U : ι → ℂ) (lam : ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (hU : ∀ i, ‖U i‖ = 1) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    {w v : ι → ℂ} (hwv : phaseMarkovOperator Q U lam w = v) :
    ‖w‖ ≤ (1 - lam)⁻¹ * ‖v‖ := by
  have hbound := phase_markov_lower_bound Q U lam hQ hrow hU hlam0 w
  rw [hwv] at hbound
  have hpos : 0 < 1 - lam := sub_pos.mpr hlam1
  calc
    ‖w‖ ≤ ‖v‖ / (1 - lam) := (le_div_iff₀ hpos).mpr (by nlinarith)
    _ = (1 - lam)⁻¹ * ‖v‖ := by rw [div_eq_mul_inv, mul_comm]

end NonSymmetricDyson.MarkovStability
