import Dyson.Full.SingularSpectralAlgebra

/-! The exact Perron eigenvalue formula of lemma F-PF, for the actual
saturated matrix and actual imaginary Dyson equation. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem perron_eigenvalue_identity
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution S a z m)
    (l : ι → ℝ) (lam : ℝ) (hl : ∀ i, 0 < l i)
    (hleft : ∀ j, ∑ i, l i * (‖m i‖*S i j*‖m j‖) = lam*l j) :
    0 < (∑ i, l i * ((m i).im/‖m i‖)) ∧
    lam = 1 - z.im * (∑ i, l i*‖m i‖) / (∑ i, l i*((m i).im/‖m i‖)) := by
  have hn : ∀ i, 0 < ‖m i‖ := fun i => norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)
  let δ : ℝ := ∑ i, l i*((m i).im/‖m i‖)
  have hδ : 0 < δ := Finset.sum_pos (fun i _ => mul_pos (hl i) (div_pos (hm i) (hn i)))
    Finset.univ_nonempty
  have hsum : ∑ i, l i * (∑ j, (‖m i‖*S i j*‖m j‖)*((m j).im/‖m j‖)) = lam*δ := by
    calc
      _ = ∑ i, ∑ j, (l i*(‖m i‖*S i j*‖m j‖))*((m j).im/‖m j‖) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j, (∑ i, l i*(‖m i‖*S i j*‖m j‖))*((m j).im/‖m j‖) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = lam*δ := by
        simp_rw [hleft, mul_assoc]
        exact (Finset.mul_sum ..).symm
  have hi : δ - lam*δ = z.im * (∑ i, l i*‖m i‖) := by
    rw [← hsum]
    dsimp [δ]
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i, l i * (z.im * ‖m i‖) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_sub, SingularSpectral.normalized_imaginary_identity S a z m
          (fun j => BasicEstimates.component_ne_zero hm j) heq i]
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  refine ⟨hδ, ?_⟩
  change lam = 1-z.im*(∑ i, l i*‖m i‖)/δ
  apply (mul_right_cancel₀ hδ.ne')
  field_simp
  linarith

theorem perron_eigenvalue_lt_one
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution S a z m)
    (l : ι → ℝ) (lam : ℝ) (hl : ∀ i, 0 < l i)
    (hleft : ∀ j, ∑ i, l i * (‖m i‖*S i j*‖m j‖) = lam*l j) : lam < 1 := by
  obtain ⟨hδ,hlam⟩ := perron_eigenvalue_identity S a z m hm heq l lam hl hleft
  have hμ : 0 < ∑ i, l i*‖m i‖ := Finset.sum_pos
    (fun i _ => mul_pos (hl i) (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)))
    Finset.univ_nonempty
  rw [hlam]
  exact sub_lt_self _ (div_pos (mul_pos hz hμ) hδ)

end NonSymmetricDyson.Full.Singularities
