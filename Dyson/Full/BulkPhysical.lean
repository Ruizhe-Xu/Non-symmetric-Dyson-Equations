import Dyson.Full.BulkSubstochastic
import Dyson.Full.BulkDistance

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkPhysical
universe u
open Resonance MarkovStability
variable {V : Type u} [Fintype V] [Nonempty V]

def rowDeficit (z : ℂ) (m : V → ℂ) (i : V) : ℝ := z.im * ‖m i‖ ^ 2 / (m i).im

theorem row_sum (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ)
    (m : V → ℂ) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : V) :
    ∑ j, BulkBoundary.boundaryMarkov S m i j = 1 - rowDeficit z m i := by
  have hh := BasicEstimates.weighted_imaginary_part_identity hm hsol i
  rw [Complex.normSq_eq_norm_sq] at hh
  simp only [BulkBoundary.boundaryMarkov, ← Finset.sum_div]
  have he : (∑ j, ‖m i‖ ^ 2 * S i j * (m j).im) =
      ‖m i‖ ^ 2 * ∑ j, S i j * (m j).im := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  unfold rowDeficit
  apply (div_eq_iff (ne_of_gt (hm i))).mpr
  field_simp [ne_of_gt (hm i)]
  nlinarith [hh]

theorem weighted_transfer (S : Matrix V V ℝ) (m : V → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (rho c D B : ℝ) (hr : 0 < rho) (hc : 0 < c) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hylo : ∀ i, c * rho ≤ (m i).im) (hyhi : ∀ i, (m i).im ≤ rho)
    (hphase : ∀ w : V → ℂ, D * ‖w‖ ≤ B *
      ‖phaseMarkovOperator (BulkBoundary.boundaryMarkov S m)
        (fun i => (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm) i : ℂ)) 1 w‖)
    (x : V → ℂ) : c * D * ‖x‖ ≤ B * ‖InteriorStability.stabilityOperator S m x‖ := by
  let w : V → ℂ := fun i => x i / ((m i).im : ℂ)
  have hwx : (fun i => ((m i).im : ℂ) * w i) = x := by
    funext i
    dsimp [w]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))]
  have hxw : ‖x‖ ≤ rho * ‖w‖ := by
    have hh := BulkAlgebra.diagonal_upper (fun i => ((m i).im : ℂ)) w rho hr.le
      (fun i => by simpa [Complex.norm_real, abs_of_pos (hm i)] using hyhi i)
    rwa [hwx] at hh
  have hup : ‖phaseMarkovOperator (BulkBoundary.boundaryMarkov S m)
      (fun i => (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm) i : ℂ)) 1 w‖ ≤
        (c * rho)⁻¹ * ‖InteriorStability.stabilityOperator S m x‖ := by
    rw [show w = (fun i => x i / ((m i).im : ℂ)) from rfl,
      BulkBoundary.boundary_conjugation S m hm x]
    apply BulkAlgebra.diagonal_upper _ _ _ (by positivity)
    intro i
    rw [norm_div, Circle.norm_coe, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hm i), one_div]
    exact inv_anti₀ (mul_pos hc hr) (hylo i)
  have hmain := (hphase w).trans (mul_le_mul_of_nonneg_left hup hB)
  have hh := mul_le_mul_of_nonneg_left hmain (mul_nonneg hc.le hr.le)
  have he : (c * rho) * (B * ((c * rho)⁻¹ * ‖InteriorStability.stabilityOperator S m x‖)) =
      B * ‖InteriorStability.stabilityOperator S m x‖ := by field_simp
  rw [he] at hh
  have hdx := mul_le_mul_of_nonneg_left hxw (mul_nonneg hc.le hD)
  nlinarith

theorem deficit_bounds (z : ℂ) (m : V → ℂ) (hm : BasicEstimates.IsUpperSolution m)
    (rho c b M : ℝ) (hr : 0 < rho) (hc : 0 < c) (hb : 0 < b)
    (hz : 0 ≤ z.im) (hylo : ∀ i, c * rho ≤ (m i).im)
    (hyhi : ∀ i, (m i).im ≤ rho) (hlo : ∀ i, b ≤ ‖m i‖)
    (hhi : ∀ i, ‖m i‖ ≤ M) (i : V) :
    z.im * b ^ 2 / rho ≤ rowDeficit z m i ∧
      rowDeficit z m i ≤ (M ^ 2 / (c * b ^ 2)) * (z.im * b ^ 2 / rho) := by
  have hbq : b ^ 2 ≤ ‖m i‖ ^ 2 := by nlinarith [hlo i, norm_nonneg (m i)]
  have hMq : ‖m i‖ ^ 2 ≤ M ^ 2 := by nlinarith [hhi i, norm_nonneg (m i)]
  unfold rowDeficit
  constructor
  · exact div_le_div₀ (mul_nonneg hz (sq_nonneg ‖m i‖))
      (mul_le_mul_of_nonneg_left hbq hz) (hm i) (hyhi i)
  · calc
      _ ≤ z.im * M ^ 2 / (c * rho) := div_le_div₀
        (mul_nonneg hz (sq_nonneg _)) (mul_le_mul_of_nonneg_left hMq hz)
        (mul_pos hc hr) (hylo i)
      _ = _ := by field_simp

theorem support_lower (S : Matrix V V ℝ) (m : V → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (rho c b s : ℝ) (hr : 0 < rho) (hc : 0 < c) (hb : 0 < b) (hs : 0 ≤ s)
    (hylo : ∀ i, c * rho ≤ (m i).im) (hyhi : ∀ i, (m i).im ≤ rho)
    (hlo : ∀ i, b ≤ ‖m i‖) (i j : V) (hS : s ≤ S i j) :
    b ^ 2 * s * c ≤ BulkBoundary.boundaryMarkov S m i j := by
  have hbq : b ^ 2 ≤ ‖m i‖ ^ 2 := by nlinarith [hlo i, norm_nonneg (m i)]
  have hm1 := mul_le_mul hbq hS hs (sq_nonneg _)
  have hm2 := mul_le_mul hm1 (hylo j) (mul_nonneg hc.le hr.le)
    (mul_nonneg (sq_nonneg _) (hs.trans hS))
  have hd := div_le_div₀ (mul_nonneg (mul_nonneg (sq_nonneg _) (hs.trans hS)) (hm j).le) hm2 (hm i) (hyhi i)
  have he : b ^ 2 * s * (c * rho) / rho = b ^ 2 * s * c := by field_simp
  simpa only [he, BulkBoundary.boundaryMarkov] using hd

/-- Quantitative transfer to the actual Dyson operator. All constants in this
statement are uniform in the supplied modulus and imaginary-part bounds. -/
theorem distance_and_height_bound (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (b M c s P : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c) (hs : 0 < s) (hP : 0 < P)
    (hsup : ∀ i j, S i j ≠ 0 → s ≤ S i j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m), BasicEstimates.IsDysonSolution S a z m →
      0 ≤ z.im → 0 < rho → rho ≤ P →
      (∀ i, c * rho ≤ (m i).im) → (∀ i, (m i).im ≤ rho) →
      (∀ i, b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) → ∀ x : V → ℂ,
      ((BulkTorus.resonanceDistance (fun i j => S i j ≠ 0)
        (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm))) ^ 2 + z.im) * ‖x‖ ≤
          C * ‖InteriorStability.stabilityOperator S m x‖ := by
  obtain ⟨cE, hcE, hphase⟩ := BulkSubstochastic.phase_distance_bound external
    (fun i j => S i j ≠ 0) hcS
  let k : ℝ := min 1 (b ^ 2 * s * c)
  have hk : 0 < k := lt_min (by norm_num) (by positivity)
  let D : ℝ := 1 + M ^ 2 / (c * b ^ 2)
  have hD : 0 < D := by positivity
  let A : ℝ := c * cE * k ^ (2 * Fintype.card V)
  have hA : 0 < A := by positivity
  refine ⟨D / A + P / (c * b ^ 2), by positivity, ?_⟩
  intro a z m rho hm hsol hz hr hP' hylo hyhi hlo hhi x
  let d0 := z.im * b ^ 2 / rho
  have hd0 : 0 ≤ d0 := by positivity
  have hds := deficit_bounds z m hm rho c b M hr hc hb hz hylo hyhi hlo hhi
  have hdc : 0 ≤ M ^ 2 / (c * b ^ 2) := by positivity
  have hps (i j : V) (hij : S i j ≠ 0) : k ≤ BulkBoundary.boundaryMarkov S m i j :=
    (min_le_right _ _).trans (support_lower S m hm rho c b s hr hc hb hs.le
      hylo hyhi hlo i j (hsup i j hij))
  let phase := BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm)
  let dist := BulkTorus.resonanceDistance (fun i j => S i j ≠ 0) phase
  have hmark := hphase (BulkBoundary.boundaryMarkov S m) (rowDeficit z m)
    (BulkBoundary.boundaryMarkov_nonnegative S m hS hm) (row_sum S a z m hm hsol)
    d0 (M ^ 2 / (c * b ^ 2)) hd0 hdc (fun i => (hds i).1) (fun i => (hds i).2)
    k hk (min_le_left _ _) hps phase
  have hdist := weighted_transfer S m hm rho c
    (cE * k ^ (2 * Fintype.card V) * dist ^ 2) D hr hc (by positivity) hD.le
    hylo hyhi hmark x
  have hdout : dist ^ 2 * ‖x‖ ≤ (D / A) * ‖InteriorStability.stabilityOperator S m x‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hA).mpr
    calc
      _ = c * (cE * k ^ (2 * Fintype.card V) * dist ^ 2) * ‖x‖ := by dsimp [A]; ring
      _ ≤ _ := hdist
  have hgap := weighted_transfer S m hm rho c d0 1 hr hc hd0 (by norm_num)
    hylo hyhi (fun w => by simpa using (BulkSubstochastic.substochastic_gap
      (BulkBoundary.boundaryMarkov S m) (rowDeficit z m)
      (BulkBoundary.boundaryMarkov_nonnegative S m hS hm) (row_sum S a z m hm hsol)
      d0 hd0 (fun i => (hds i).1) phase w)) x
  have hheight : z.im * ‖x‖ ≤ (P / (c * b ^ 2)) * ‖InteriorStability.stabilityOperator S m x‖ := by
    have hg := mul_le_mul_of_nonneg_left hgap hr.le
    have he : rho * (c * d0 * ‖x‖) = c * b ^ 2 * (z.im * ‖x‖) := by dsimp [d0]; field_simp
    rw [he, one_mul] at hg
    have hpN := mul_le_mul_of_nonneg_right hP' (norm_nonneg (InteriorStability.stabilityOperator S m x))
    have hg' := hg.trans hpN
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < c * b ^ 2)).mpr
    nlinarith
  dsimp [dist, phase] at hdout
  nlinarith

end NonSymmetricDyson.Full.BulkPhysical
