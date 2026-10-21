import Dyson.Full.EuclideanInverse

/-! The original rough linear stability proposition, including unbounded
real energies. The bound is C(1+η⁻¹), not the weaker η⁻² bound used for
fixed positive-height rectangles. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Linear
open InteriorStability
variable {ι : Type*} [Fintype ι]

theorem bounded_modulus_lower_norm_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (b M : ℝ) (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hb : 0 < b) (hM : 0 ≤ M)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hlo : ∀ i, b ≤ ‖m i‖) (hhi : ∀ i, ‖m i‖ ≤ M) (u : ι → ℂ) :
    ‖u‖ ≤ (M / b^2) * z.im⁻¹ * ‖stabilityOperator S m u‖ := by
  let C := ‖stabilityOperator S m u‖ / (z.im*b^2)
  have hden : 0 < z.im*b^2 := by positivity
  have hC : 0 ≤ C := div_nonneg (norm_nonneg _) hden.le
  have hf : ∀ i, ‖stabilityOperator S m u i‖ ≤ C*z.im*‖m i‖^2 := by
    intro i
    calc
      _ ≤ ‖stabilityOperator S m u‖ := norm_le_pi_norm _ _
      _ = C*(z.im*b^2) := (div_mul_cancel₀ _ hden.ne').symm
      _ ≤ C*(z.im*‖m i‖^2) := by gcongr; exact hlo i
      _ = _ := by ring
  have hw := weighted_stability_estimate hS hz hm hsol u C hf
  have hu : ‖u‖ ≤ C*M := (pi_norm_le_iff_of_nonneg (mul_nonneg hC hM)).mpr
    (fun i => (hw i).trans (mul_le_mul_of_nonneg_left
      ((Complex.im_le_norm _).trans (hhi i)) hC))
  exact hu.trans_eq (by dsimp [C]; ring)

/-- Uniform C(1+η⁻¹) in the ordinary Euclidean operator norm, from the
scaled component estimates proved in M3. All constants precede the point
and solution; no compactness of the unbounded strip is assumed. -/
theorem rough_inverse_bound_of_scaled_components
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (b M R : ℝ) (hb : 0 < b) (hM : 0 < M) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, S i j ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : ι → ℂ) (hz : 0 < z.im)
      (hm : BasicEstimates.IsUpperSolution m)
      (hsol : BasicEstimates.IsDysonSolution S a z m),
      (∀ i, b ≤ (1+‖z‖)*‖m i‖) → (∀ i, (1+‖z‖)*‖m i‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤ C*(1+z.im⁻¹) := by
  let Z : ℝ := 1+M^2*R
  let b₀ : ℝ := b/(1+Z)
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  let A := max 2 (M/b₀^2)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let C := 1+Real.sqrt (Fintype.card ι)*A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro z m hz hm hsol hlo hhi
  have hd : 0 < 1+‖z‖ := by positivity
  have hup (i : ι) : ‖m i‖ ≤ M/(1+‖z‖) := (le_div_iff₀ hd).mpr (by simpa [mul_comm] using hhi i)
  have hupM (i : ι) : ‖m i‖ ≤ M := (hup i).trans (div_le_self hM.le (by linarith [norm_nonneg z]))
  have ha : 0 ≤ A*(1+z.im⁻¹) := by positivity
  have hbound : ∀ u, ‖u‖ ≤ (A*(1+z.im⁻¹))*‖stabilityOperator S m u‖ := by
    intro u
    by_cases hnear : ‖z‖ ≤ Z
    · have hlow (i : ι) : b₀ ≤ ‖m i‖ := by
        apply (div_le_iff₀ (by positivity : 0<1+Z)).mpr
        simpa only [mul_comm] using (hlo i).trans
          (mul_le_mul_of_nonneg_right (add_le_add_left hnear 1) (norm_nonneg (m i)))
      have h := bounded_modulus_lower_norm_bound S a z m b₀ M hS hz hb₀ hM.le hm hsol hlow hupM u
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        (M/b₀^2)*z.im⁻¹ ≤ A*z.im⁻¹ := mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr hz.le)
        _ ≤ A*(1+z.im⁻¹) := by nlinarith
    · have hfar : Z < ‖z‖ := lt_of_not_ge hnear
      have hsq : 2*M^2*R ≤ (1+‖z‖)^2 := by
        have hx : 0 ≤ M^2*R := by positivity
        have hbase : 2*M^2*R ≤ Z^2 := by dsimp [Z]; nlinarith [sq_nonneg (M^2*R)]
        have hzn : Z^2 ≤ (1+‖z‖)^2 := by nlinarith
        exact hbase.trans hzn
      have hrows (i : ι) : ‖m i‖^2*(∑ j, S i j) ≤ (1:ℝ)/2 := by
        calc
          _ ≤ (M/(1+‖z‖))^2*R := mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg _) (hup i) 2) (hrow i)
            (Finset.sum_nonneg fun j _ => hS i j) (sq_nonneg _)
          _ ≤ 1/2 := by
            rw [div_pow, div_mul_eq_mul_div]
            apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
            nlinarith
      have h := row_lower_norm_bound S m (1/2) hS (by norm_num) hrows u
      have hh : ‖u‖ ≤ 2*‖stabilityOperator S m u‖ := by norm_num at h ⊢; linarith
      exact hh.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_mul_of_one_le_right hA.le
          (by linarith [inv_pos.mpr hz]))) (norm_nonneg _))
  have he := EuclideanInverse.stability_inverse_upper S a z m hS hz hm hsol
    (A*(1+z.im⁻¹)) ha hbound
  exact he.trans (by dsimp [C]; nlinarith [inv_nonneg.mpr hz.le])

end NonSymmetricDyson.Full.Linear
