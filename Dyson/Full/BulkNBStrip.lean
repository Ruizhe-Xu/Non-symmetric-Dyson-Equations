import Dyson.Full.BulkNBQuantitative
import Dyson.Full.BulkStrip

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkNBStrip
universe u
open Resonance Nonbacktracking BulkQuantitative
variable {V : Type u} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

theorem support_eq : (fun e f => G.matrix e f ≠ 0) = G.CanFollow := by
  funext e f
  apply propext
  by_cases h : G.CanFollow e f <;> simp [BaseGraph.matrix, h]

theorem uniform_shift_bound
    (M c P B : ℝ) (hM : 0 < M) (hc : 0 < c) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge) (hconn : StronglyConnected G.CanFollow)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (hz : 0 ≤ z.im) (hr : 0 < rho) (hrP : rho ≤ P)
    (hy : ∀ e, c * rho ≤ (m e).im) (hn : ∀ e, ‖m e‖ ≤ M)
    (hshift : ∀ y, ‖z - (a y : ℂ)‖ ≤ B) :
    c * rho * ‖fun y => z - (a y : ℂ)‖ ≤
      ((Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2 + M * B + M + c * P) *
        (BulkTorus.resonanceDistance (fun e f => G.matrix e f ≠ 0)
          (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm)) + z.im) := by
  letI : Nonempty G.Edge := ⟨root⟩
  let phase := positivePhase m (BasicEstimates.component_ne_zero hm)
  let delta := BulkTorus.resonanceDistance G.CanFollow phase
  have hd0 : 0 ≤ delta := BulkTorus.resonanceDistance_nonnegative G.CanFollow phase
  obtain ⟨v, hv, he⟩ := BulkDistance.exists_nearest G.CanFollow phase
  have herr (e : G.Edge) : ‖(phase e : ℂ) - (v e : ℂ)‖ ≤ delta := by
    have hh := norm_le_pi_norm (BulkTorus.difference phase v) e
    simpa only [he] using hh
  let A := (Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2 + M * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let D := A * delta + (M + c * rho) * z.im
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoords : ‖(c * rho) • (fun y => z - (a y : ℂ))‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro y
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hr.le)]
    exact BulkNBQuantitative.NB.shift_bound G a z m hm hsol hd root hconn rho c M B delta
      hr hc hM hB hd0 hz hy hn hshift v hv herr y
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le hr.le)] at hcoords
  have hup : D ≤ (A + M + c * P) * (delta + z.im) := by
    dsimp [D]
    have hp := mul_le_mul_of_nonneg_left hrP hc.le
    have hpz := mul_le_mul_of_nonneg_right hp hz
    have hx1 : 0 ≤ (M + c * P) * delta := by positivity
    have hx2 : 0 ≤ A * z.im := by positivity
    nlinarith
  have hh := hcoords.trans hup
  rw [support_eq G, ← BulkStrip.positive_distance]
  exact hh

/-- Quantitative non-backtracking strip estimate with terminal shifts. -/
theorem strip_bound
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge) (hbase : StronglyConnected G.Adj)
    (b M c P B H : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hP : 0 < P) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m),
      BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m →
      0 ≤ z.im → z.im ≤ H → 0 < rho → rho ≤ P →
      (∀ e, c * rho ≤ (m e).im) → (∀ e, (m e).im ≤ rho) →
      (∀ e, b ≤ ‖m e‖) → (∀ e, ‖m e‖ ≤ M) →
      (∀ y, ‖z - (a y : ℂ)‖ ≤ B) → ∀ x : G.Edge → ℂ,
      (rho * ‖fun y => z - (a y : ℂ)‖) ^ 2 * ‖x‖ ≤
        C * ‖InteriorStability.stabilityOperator G.matrix m x‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  have hconn := BulkConnectivity.NB.stronglyConnected G hd hbase
  have hcS : StronglyConnected (fun e f => G.matrix e f ≠ 0) := by rw [support_eq]; exact hconn
  have hsupport (e f : G.Edge) (h : G.matrix e f ≠ 0) : (1 : ℝ) ≤ G.matrix e f := by
    unfold BaseGraph.matrix at h ⊢
    split_ifs with hh
    · norm_num
    · exact False.elim (h (by simp [hh]))
  obtain ⟨C0, hC0, hbound⟩ := BulkPhysical.distance_and_height_bound external G.matrix
    G.matrix_nonnegative hcS b M c 1 P hb hM hc (by norm_num) hP hsupport
  let K := (Fintype.card G.Edge : ℝ) * 3 * (1 + M ^ 2) ^ 2 * M ^ 2 + M * B + M + c * P
  have hK : 0 < K := by dsimp [K]; positivity
  let D := 2 * K ^ 2 * max 1 H / c ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * C0, mul_pos hD hC0, ?_⟩
  intro a z m rho hm hsol hz hzH hr hrP hylo hyhi hlo hhi hshift x
  have ht := uniform_shift_bound G M c P B hM hc hP.le hB a z m rho hd root hconn
    hm hsol hz hr hrP hylo hhi hshift
  have hsquare := BulkStrip.squared_shift_bound c K H rho ‖fun y => z - (a y : ℂ)‖
    (BulkTorus.resonanceDistance (fun e f => G.matrix e f ≠ 0)
      (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm))) z.im
    hc hK.le hH hr.le (norm_nonneg _) (BulkTorus.resonanceDistance_nonnegative _ _) hz hzH ht
  have hphys := hbound (G.terminalShift a) z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  have h1 := mul_le_mul_of_nonneg_right hsquare (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hphys hD.le
  dsimp [D] at h2
  nlinarith

end NonSymmetricDyson.Full.BulkNBStrip
