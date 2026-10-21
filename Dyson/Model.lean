import Dyson.Algebra
import Dyson.BasicEstimates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Concrete finite-matrix interface to the algebraic module.
All operations have the manuscript's convention `-1/m = z - a + S m`.
`WellPosednessTarget` is the proposition interface whose proof is supplied in
`Dyson.GlobalWellPosedness`.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.Model

variable {ι : Type*} [Fintype ι]

/-- Real coefficients act on complex-valued coordinate vectors. -/
def action (S : Matrix ι ι ℝ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.mulVecLin (fun i j => (S i j : ℂ) : Matrix ι ι ℂ)

theorem action_apply (S : Matrix ι ι ℝ) (m : ι → ℂ) (i : ι) :
    action S m i = ∑ j, (S i j : ℂ) * m j := rfl

/-- Dyson residual, including a general real shift `a`.
For `a = 0` this is exactly `eq.Dyson-residual`. -/
def residual (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (g : ι → ℂ) : ι → ℂ :=
  fun i => -(g i)⁻¹ - (z - (a i : ℂ)) - action S g i

theorem residual_zero_iff (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z : ℂ) (m : ι → ℂ) :
    residual S a z m = 0 ↔ BasicEstimates.IsDysonSolution S a z m := by
  constructor
  · intro h i
    have hi := congrFun h i
    simp only [residual, Pi.zero_apply, action_apply] at hi
    linear_combination hi
  · intro h
    ext i
    have hi := h i
    simp only [residual, Pi.zero_apply, action_apply]
    linear_combination hi

/-- The exact perturbation identity with the residual computed from `g`.
Unlike the analytic stability theorems, this identity requires no smallness. -/
theorem exact_residual_expansion (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z : ℂ) (m g : ι → ℂ)
    (hm : BasicEstimates.IsDysonSolution S a z m)
    (hm0 : ∀ i, m i ≠ 0) (hg0 : ∀ i, g i ≠ 0) :
    DysonPaper.Algebra.stabilityAction m (action S) (g - m) =
      fun i => m i ^ 2 * residual S a z g i + (g i - m i) ^ 2 / g i := by
  apply DysonPaper.Algebra.dyson_displacement m g (fun i => z - (a i : ℂ))
    (residual S a z g) (action S) hm0 hg0
  · intro i
    exact hm i
  · intro i
    simp only [residual]
    ring

/-- The pointwise existence-and-uniqueness assertion of
`thm:Existence and uniqueness`, proved in `Dyson.GlobalWellPosedness`.
Analyticity and measure representations are separate assertions. -/
def WellPosednessTarget (S : Matrix ι ι ℝ) (a : ι → ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    ∃! m : ι → ℂ, BasicEstimates.IsUpperSolution m ∧
      BasicEstimates.IsDysonSolution S a z m

end NonSymmetricDyson.Model
