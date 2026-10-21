import Mathlib

/-! Explicit comparison between the manuscript's unnormalized Euclidean norm
and Lean's supremum norm on a finite function space. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Norms

variable {ι : Type*} [Fintype ι]

def euclideanNorm (u : ι → ℂ) : ℝ := ‖WithLp.toLp 2 u‖

theorem sup_le_euclidean (u : ι → ℂ) : ‖u‖ ≤ euclideanNorm u := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (WithLp.toLp 2 u))).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 u) i

theorem euclidean_le_sqrt_card_mul_sup (u : ι → ℂ) :
    euclideanNorm u ≤ Real.sqrt (Fintype.card ι) * ‖u‖ := by
  have hsum : (∑ i, ‖u i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * ‖u‖ ^ 2 := by
    calc
      (∑ i, ‖u i‖ ^ 2) ≤ ∑ _ : ι, ‖u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u i) 2
      _ = _ := by simp
  have hn := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 u)
  have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) by positivity)
  have hpos : 0 ≤ Real.sqrt (Fintype.card ι) * ‖u‖ := by positivity
  dsimp [euclideanNorm]
  simp only [PiLp.toLp_apply] at hn
  nlinarith [norm_nonneg (WithLp.toLp 2 u)]

/-- A supremum lower bound yields the Euclidean lower bound with an explicit
dimension constant; in particular there is no implicit normalization by d. -/
theorem transfer_lower_bound (L : (ι → ℂ) → (ι → ℂ)) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ u, ‖u‖ ≤ C * ‖L u‖) (u : ι → ℂ) :
    euclideanNorm u ≤ (Real.sqrt (Fintype.card ι) * C) * euclideanNorm (L u) := by
  calc
    euclideanNorm u ≤ Real.sqrt (Fintype.card ι) * ‖u‖ :=
      euclidean_le_sqrt_card_mul_sup u
    _ ≤ Real.sqrt (Fintype.card ι) * (C * ‖L u‖) :=
      mul_le_mul_of_nonneg_left (h u) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (Fintype.card ι) * (C * euclideanNorm (L u)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sup_le_euclidean (L u)) hC) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Elementary perturbation absorption, used to extend a real-axis inverse
bound to a uniform strip of positive heights. -/
theorem perturbation_lower_bound {E : Type*} [SeminormedAddCommGroup E]
    (L M : E → E) (C δ : ℝ) (hC : 0 ≤ C) (hδ : C * δ < 1)
    (hL : ∀ u, ‖u‖ ≤ C * ‖L u‖)
    (hclose : ∀ u, ‖L u - M u‖ ≤ δ * ‖u‖) (u : E) :
    ‖u‖ ≤ C / (1 - C * δ) * ‖M u‖ := by
  have ht : ‖L u‖ ≤ ‖M u‖ + δ * ‖u‖ := by
    calc
      ‖L u‖ = ‖M u + (L u - M u)‖ := by congr 1; abel
      _ ≤ ‖M u‖ + ‖L u - M u‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left (hclose u) _
  have hh : (1 - C * δ) * ‖u‖ ≤ C * ‖M u‖ := by
    have hp := mul_le_mul_of_nonneg_left ht hC
    nlinarith [hL u]
  have hd : 0 < 1 - C * δ := sub_pos.mpr hδ
  calc
    ‖u‖ ≤ (C * ‖M u‖) / (1 - C * δ) :=
      (le_div_iff₀ hd).mpr (by nlinarith)
    _ = _ := by ring

end NonSymmetricDyson.Full.Norms
