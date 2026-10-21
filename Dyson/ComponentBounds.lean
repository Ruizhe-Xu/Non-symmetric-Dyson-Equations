import Dyson.BasicEstimates
import Mathlib

/-!
Explicit component bounds for actual Dyson solutions.
Under a uniform bound on m and a bounded real part of z these prove the
modulus comparison in thm.bound throughout the open upper half-plane.
-/

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.ComponentBounds
variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ} {m : ι → ℂ}

/-- A direct lower bound from the Dyson equation; no irreducibility is needed. -/
theorem inverse_norm_le (hS : ∀ i j, 0 ≤ S i j)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    ‖m i‖⁻¹ ≤ ‖z‖ + |a i| + ∑ j, S i j * ‖m j‖ := by
  calc
    ‖m i‖⁻¹ = ‖-(m i)⁻¹‖ := by simp
    _ = ‖z - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j‖ := by rw [hsol i]
    _ ≤ ‖z - (a i : ℂ)‖ + ‖∑ j, (S i j : ℂ) * m j‖ := norm_add_le _ _
    _ ≤ (‖z‖ + ‖(a i : ℂ)‖) + ∑ j, ‖(S i j : ℂ) * m j‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ = ‖z‖ + |a i| + ∑ j, S i j * ‖m j‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hS i j)]

/-- Explicit lower half of the paper's modulus comparison. -/
theorem uniform_lower_bound (hS : ∀ i j, 0 ≤ S i j)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j, ‖m j‖ ≤ M) (i : ι) :
    (1 + |a i| + M * ∑ j, S i j)⁻¹ / (1 + ‖z‖) ≤ ‖m i‖ := by
  have hrow : 0 ≤ ∑ j, S i j := Finset.sum_nonneg (fun j _ => hS i j)
  have hc : 0 < 1 + |a i| + M * ∑ j, S i j := by positivity
  have hz : 0 < 1 + ‖z‖ := by positivity
  have hmpos : 0 < ‖m i‖ := norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)
  have h := inverse_norm_le hS hsol i
  have hsum : (∑ j, S i j * ‖m j‖) ≤ M * ∑ j, S i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [hbound j, hS i j]
  have hinv : ‖m i‖⁻¹ ≤ (1 + |a i| + M * ∑ j, S i j) * (1 + ‖z‖) := by
    nlinarith [norm_nonneg z, abs_nonneg (a i), mul_nonneg hM hrow]
  have hone : 1 ≤ ((1 + |a i| + M * ∑ j, S i j) * (1 + ‖z‖)) * ‖m i‖ := by
    calc
      1 = ‖m i‖⁻¹ * ‖m i‖ := (inv_mul_cancel₀ hmpos.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv hmpos.le
  have : 1 / ((1 + |a i| + M * ∑ j, S i j) * (1 + ‖z‖)) ≤ ‖m i‖ :=
    (div_le_iff₀ (mul_pos hc hz)).mpr (by simpa only [mul_comm] using hone)
  simpa only [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, one_mul] using this

/-- Explicit upper half of the modulus comparison on a bounded real strip. -/
theorem uniform_upper_bound (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    {M T : ℝ} (hT : 0 ≤ T) (hreal : |z.re| ≤ T)
    (hbound : ∀ j, ‖m j‖ ≤ M) (i : ι) :
    ‖m i‖ ≤ ((1 + T) * M + 1) / (1 + ‖z‖) := by
  have hrough := BasicEstimates.rough_bound hS hz hm hsol i
  have heta : ‖m i‖ * z.im ≤ 1 := (le_div_iff₀ hz).mp (by simpa only [one_div] using hrough)
  have hznorm : ‖z‖ ≤ |z.re| + z.im := by
    simpa only [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im z
  apply (le_div_iff₀ (by positivity : 0 < 1 + ‖z‖)).mpr
  have hnorm : 0 ≤ ‖m i‖ := norm_nonneg _
  have h1 : ‖m i‖ * (1 + ‖z‖) ≤ ‖m i‖ * (1 + T + z.im) := by
    apply mul_le_mul_of_nonneg_left _ hnorm
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (hbound i) (by positivity : 0 ≤ 1 + T)]

/-- A positive model-dependent constant uniform over all coordinates. -/
def uniformLowerConstant (S : ι → ι → ℝ) (a : ι → ℝ) (M : ℝ) : ℝ :=
  (1 + ∑ i, |a i| + M * ∑ i, ∑ j, S i j)⁻¹

theorem uniformLowerConstant_pos (hS : ∀ i j, 0 ≤ S i j) {M : ℝ} (hM : 0 ≤ M) :
    0 < uniformLowerConstant S a M := by
  unfold uniformLowerConstant
  apply inv_pos.mpr
  have hr : 0 ≤ ∑ i, ∑ j, S i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hS i j))
  positivity

/-- The same explicit lower constant works for every component and every z. -/
theorem common_scaled_lower_bound (hS : ∀ i j, 0 ≤ S i j)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ j, ‖m j‖ ≤ M) (i : ι) :
    uniformLowerConstant S a M / (1 + ‖z‖) ≤ ‖m i‖ := by
  have hra : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hrs : (∑ j, S i j) ≤ ∑ k, ∑ j, S k j :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hS k j))
      (Finset.mem_univ i)
  have hr : 0 ≤ ∑ j, S i j := Finset.sum_nonneg (fun j _ => hS i j)
  have hden : 0 < 1 + |a i| + M * ∑ j, S i j := by positivity
  have hdenle : 1 + |a i| + M * ∑ j, S i j ≤
      1 + ∑ j, |a j| + M * ∑ k, ∑ j, S k j := by
    nlinarith [mul_le_mul_of_nonneg_left hrs hM]
  have hinv : uniformLowerConstant S a M ≤ (1 + |a i| + M * ∑ j, S i j)⁻¹ := by
    simpa only [uniformLowerConstant, one_div] using one_div_le_one_div_of_le hden hdenle
  exact (div_le_div_of_nonneg_right hinv (by positivity)).trans
    (uniform_lower_bound hS hm hsol hM hbound i)

end NonSymmetricDyson.ComponentBounds
