import Dyson.Full.NonlinearModel

noncomputable section

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

/-- The rough regime for actual Dyson vectors. Both the approximate solution
and the physical solution are controlled by the already constructed scalar
reduction; no root or branch choice is assumed. -/
theorem actual_point_rough_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ z : ℂ) (mτ m g p q r : ι → ℂ)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (k : ℕ) (D : LocalReduction F K ℓ p q r k)
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hmτ : BasicEstimates.IsDysonSolution S a τ mτ)
    (hmτ0 : ∀ i, mτ i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * mτ i)
    (hm : BasicEstimates.IsUpperSolution m)
    (heqm : BasicEstimates.IsDysonSolution S a z m) (hg0 : ∀ i, g i ≠ 0)
    (hgsmall : ‖normalized q mτ g‖ < D.radius)
    (hmsmall : ‖normalized q mτ m‖ < D.radius)
    (hξg : ‖(z - τ) • (1 : ι → ℂ) + Model.residual S a z g‖ < D.radius)
    (hξm : ‖(z - τ) • (1 : ι → ℂ)‖ < D.radius)
    (E : ℝ) (hE : 0 ≤ E) (hR : ‖Model.residual S a z g‖ ≤ E) :
    ‖g - m‖ ≤ (2 * ‖q‖ * D.roughConstant) * (‖z - τ‖ + E) ^ ((1 : ℝ) / k) := by
  have hzero : Model.residual S a z m = 0 := (Model.residual_zero_iff S a z m).mpr heqm
  have heqg := normalized_dyson_residual S a τ z mτ g p q F hF hmτ hmτ0 hg0 hq0 hp hq
  have heqphys : normalized q mτ m - F (normalized q mτ m) =
      quadraticNonlinearity F p q (normalized q mτ m) ((z - τ) • (1 : ι → ℂ)) := by
    simpa only [hzero, add_zero] using normalized_dyson_residual S a τ z mτ m p q F hF
      hmτ hmτ0 (BasicEstimates.component_ne_zero hm) hq0 hp hq
  have hone : ‖(1 : ι → ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => by simp)
  have hω : ‖(z - τ) • (1 : ι → ℂ)‖ ≤ ‖z - τ‖ := by
    rw [norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (norm_nonneg (z - τ))
  have hξbound : ‖(z - τ) • (1 : ι → ℂ) + Model.residual S a z g‖ ≤ ‖z - τ‖ + E :=
    (norm_add_le _ _).trans (add_le_add hω hR)
  have hgrough : ‖normalized q mτ g‖ ≤ D.roughConstant * (‖z - τ‖ + E) ^ ((1 : ℝ) / k) := by
    have hh := D.rough (normalized q mτ g) ((z - τ) • (1 : ι → ℂ) + Model.residual S a z g)
      hgsmall hξg heqg
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hξbound (by positivity)) D.roughConstant_pos.le)
  have hmrough : ‖normalized q mτ m‖ ≤ D.roughConstant * (‖z - τ‖ + E) ^ ((1 : ℝ) / k) := by
    have hh := D.rough (normalized q mτ m) ((z - τ) • (1 : ι → ℂ)) hmsmall hξm heqphys
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hω.trans (le_add_of_nonneg_right hE))
        (by positivity)) D.roughConstant_pos.le)
  have hid : g - m = q * (normalized q mτ g - normalized q mτ m) := by
    have hg := normalized_reconstruction q mτ g hq0
    have hm := normalized_reconstruction q mτ m hq0
    rw [mul_sub]
    linear_combination hg - hm
  rw [hid]
  calc
    _ ≤ ‖q‖ * ‖normalized q mτ g - normalized q mτ m‖ := norm_mul_le _ _
    _ ≤ ‖q‖ * (‖normalized q mτ g‖ + ‖normalized q mτ m‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖q‖ * (D.roughConstant * (‖z - τ‖ + E) ^ ((1 : ℝ) / k) +
        D.roughConstant * (‖z - τ‖ + E) ^ ((1 : ℝ) / k)) :=
      mul_le_mul_of_nonneg_left (add_le_add hgrough hmrough) (norm_nonneg _)
    _ = _ := by ring

end NonSymmetricDyson.Full.Nonlinear
