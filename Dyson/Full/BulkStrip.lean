import Dyson.Full.BulkPhysical
import Dyson.Full.BulkQuantitative

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkStrip
universe u
open Resonance BulkQuantitative
variable {V : Type u} [Fintype V] [Nonempty V]

theorem positive_distance (E : V → V → Prop) (m : V → ℂ) (hm : ∀ i, m i ≠ 0) :
    BulkTorus.resonanceDistance E (positivePhase m hm) =
      BulkTorus.resonanceDistance E (BulkTransfer.dysonPhase m hm) := by
  have he : BulkTransfer.dysonPhase m hm = fun i => (positivePhase m hm i)⁻¹ := by
    funext i
    exact inv_pow (BulkPhase.normalize (m i) (hm i)) 2
  rw [he]
  exact (BulkDistance.inverse_distance E (positivePhase m hm)).symm

theorem squared_shift_bound (c K H rho A delta eta : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hH : 0 ≤ H) (hr : 0 ≤ rho) (hA : 0 ≤ A)
    (hd : 0 ≤ delta) (he : 0 ≤ eta) (heH : eta ≤ H)
    (h : c * rho * A ≤ K * (delta + eta)) :
    (rho * A) ^ 2 ≤ (2 * K ^ 2 * max 1 H / c ^ 2) * (delta ^ 2 + eta) := by
  have hs : (c * rho * A) ^ 2 ≤ (K * (delta + eta)) ^ 2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr h
  have he2 : eta ^ 2 ≤ H * eta := by nlinarith
  have hmH : H ≤ max 1 H := le_max_right _ _
  have hm1 : 1 ≤ max 1 H := le_max_left _ _
  have hsum : (delta + eta) ^ 2 ≤ 2 * max 1 H * (delta ^ 2 + eta) := by
    have hh1 := mul_le_mul_of_nonneg_right hm1 (sq_nonneg delta)
    have hh2 := mul_le_mul_of_nonneg_right hmH he
    nlinarith [sq_nonneg (delta - eta)]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg K)
  have hmain : c ^ 2 * (rho * A) ^ 2 ≤ (2 * K ^ 2 * max 1 H) * (delta ^ 2 + eta) := by
    nlinarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
  nlinarith

theorem symmetric_uniform_shift_bound
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (M c R P : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hR : 0 ≤ R) (hP : 0 ≤ P)
    (hrow : ∀ i, ∑ j, S i j ≤ R)
    (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ)
    (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hz : 0 ≤ z.im) (hr : 0 ≤ rho) (hrP : rho ≤ P)
    (hy : ∀ i, c * rho ≤ (m i).im) (hn : ∀ i, ‖m i‖ ≤ M) :
    c * rho * ‖fun i => z - (a i : ℂ)‖ ≤
      (R * M ^ 2 + M + c * P) *
        (BulkTorus.resonanceDistance (fun i j => S i j ≠ 0)
          (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm)) + z.im) := by
  let E := fun i j => S i j ≠ 0
  let phase := positivePhase m (BasicEstimates.component_ne_zero hm)
  let delta := BulkTorus.resonanceDistance E phase
  have hd : 0 ≤ delta := BulkTorus.resonanceDistance_nonnegative E phase
  obtain ⟨v, hv, he⟩ := BulkDistance.exists_nearest E phase
  have herr (i : V) : ‖(phase i : ℂ) - (v i : ℂ)‖ ≤ delta := by
    have hh := norm_le_pi_norm (BulkTorus.difference phase v) i
    simpa only [he] using hh
  let B := R * M ^ 2 * delta + (M + c * rho) * z.im
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcoords : ‖(c * rho) • (fun i => z - (a i : ℂ))‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hr)]
    exact symmetric_shift_bound S a z m hS hsymm hm hsol rho c M R delta
      hr hc hM hR hd hz hy hn hrow v hv herr i
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hr)] at hcoords
  have hup : B ≤ (R * M ^ 2 + M + c * P) * (delta + z.im) := by
    dsimp [B]
    have hp := mul_le_mul_of_nonneg_left hrP hc.le
    have hpz := mul_le_mul_of_nonneg_right hp hz
    have hx1 : 0 ≤ (M + c * P) * delta := by positivity
    have hx2 : 0 ≤ R * M ^ 2 * z.im := by positivity
    nlinarith
  have hh := hcoords.trans hup
  simpa only [E, delta, phase, positive_distance] using hh

/-- The original quantitative symmetric strip estimate, expressed as
coercivity of the actual stability operator. Inversion yields C/(rho*A)^2. -/
theorem symmetric_strip_bound
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (b M c s P R H : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hs : 0 < s) (hP : 0 < P) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsup : ∀ i j, S i j ≠ 0 → s ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m), BasicEstimates.IsDysonSolution S a z m →
      0 ≤ z.im → z.im ≤ H → 0 < rho → rho ≤ P →
      (∀ i, c * rho ≤ (m i).im) → (∀ i, (m i).im ≤ rho) →
      (∀ i, b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) → ∀ x : V → ℂ,
      (rho * ‖fun i => z - (a i : ℂ)‖) ^ 2 * ‖x‖ ≤
        C * ‖InteriorStability.stabilityOperator S m x‖ := by
  obtain ⟨C0, hC0, hbound⟩ := BulkPhysical.distance_and_height_bound external S hS hcS
    b M c s P hb hM hc hs hP hsup
  let K := R * M ^ 2 + M + c * P
  have hK : 0 < K := by dsimp [K]; positivity
  let D := 2 * K ^ 2 * max 1 H / c ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * C0, mul_pos hD hC0, ?_⟩
  intro a z m rho hm hsol hz hzH hr hrP hylo hyhi hlo hhi x
  have ht := symmetric_uniform_shift_bound S hS hsymm M c R P hM.le hc hR hP.le hrow
    a z m rho hm hsol hz hr.le hrP hylo hhi
  have hsquare := squared_shift_bound c K H rho ‖fun i => z - (a i : ℂ)‖
    (BulkTorus.resonanceDistance (fun i j => S i j ≠ 0)
      (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm))) z.im
    hc hK.le hH hr.le (norm_nonneg _) (BulkTorus.resonanceDistance_nonnegative _ _) hz hzH ht
  have hphys := hbound a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  have h1 := mul_le_mul_of_nonneg_right hsquare (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hphys hD.le
  dsimp [D] at h2
  nlinarith


/-- The stronger non-bipartite symmetric strip estimate C/rho². -/
theorem symmetric_nonbipartite_bound
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (b M c s P : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hs : 0 < s) (hP : 0 < P)
    (hsup : ∀ i j, S i j ≠ 0 → s ≤ S i j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m), BasicEstimates.IsDysonSolution S a z m →
      0 ≤ z.im → 0 < rho → rho ≤ P →
      (∀ i, c * rho ≤ (m i).im) → (∀ i, (m i).im ≤ rho) →
      (∀ i, b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) → ∀ x : V → ℂ,
      rho ^ 2 * ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator S m x‖ := by
  obtain ⟨C0, hC0, hbound⟩ := BulkPhysical.distance_and_height_bound external S hS hcS
    b M c s P hb hM hc hs hP hsup
  let D := M ^ 2 / (4 * c ^ 2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * C0, mul_pos hD hC0, ?_⟩
  intro a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  let E := fun i j => S i j ≠ 0
  let phase := positivePhase m (BasicEstimates.component_ne_zero hm)
  let dist := BulkTorus.resonanceDistance E phase
  let i : V := Classical.arbitrary V
  have him : (BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i) : ℂ).im =
      (m i).im / ‖m i‖ := by
    change (m i / (‖m i‖ : ℂ)).im = _
    rw [Complex.div_ofReal_im]
  have hdistance : 2 * c * rho / M ≤ dist := by
    have hlow := div_le_div₀ (hm i).le (hylo i)
      (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)) (hhi i)
    have hn := norm_le_pi_norm (BulkTorus.difference phase 1) i
    change ‖(BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i) : ℂ) ^ 2 - 1‖ ≤ _ at hn
    rw [unit_square_im, him, abs_of_pos (div_pos (hm i)
      (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)))] at hn
    rw [← BulkDistance.nonbipartite_distance E hsymm hcS hnb phase] at hn
    dsimp [dist]
    calc
      _ = 2 * (c * rho / M) := by ring
      _ ≤ 2 * ((m i).im / ‖m i‖) := mul_le_mul_of_nonneg_left hlow (by norm_num)
      _ ≤ _ := hn
  have hd0 : 0 ≤ dist := BulkTorus.resonanceDistance_nonnegative E phase
  have hd' : 2 * c * rho ≤ dist * M := (div_le_iff₀ hM).mp hdistance
  have hsquare : rho ^ 2 ≤ D * dist ^ 2 := by
    have hsq : (2 * c * rho) ^ 2 ≤ (dist * M) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hd'
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * c ^ 2)).mpr
    nlinarith
  have hphys := hbound a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  rw [← positive_distance] at hphys
  change (dist ^ 2 + z.im) * ‖x‖ ≤ C0 * ‖InteriorStability.stabilityOperator S m x‖ at hphys
  have h1 := mul_le_mul_of_nonneg_right hsquare (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hphys hD.le
  have hn : 0 ≤ D * z.im * ‖x‖ := by positivity
  nlinarith

end NonSymmetricDyson.Full.BulkStrip
