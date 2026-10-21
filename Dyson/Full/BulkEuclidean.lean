import Dyson.Full.BulkStrip
import Dyson.Full.BulkNBStrip
import Dyson.Full.BulkNBNonbip
import Dyson.Full.EuclideanInverse

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkEuclidean
universe u
open Resonance Nonbacktracking
variable {V : Type u} [Fintype V] [Nonempty V]

theorem shift_norm_pos (a : V → ℝ) (z : ℂ) (hz : 0 < z.im) :
    0 < ‖fun i => z - (a i : ℂ)‖ := by
  let i : V := Classical.arbitrary V
  have hh := (le_abs_self (z - (a i : ℂ)).im).trans (Complex.abs_im_le_norm _)
  have hh' : z.im ≤ ‖z - (a i : ℂ)‖ := by simpa using hh
  exact hz.trans_le (hh'.trans (norm_le_pi_norm (fun i => z - (a i : ℂ)) i))

theorem inverse_of_scaled_coercivity
    (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (scale C : ℝ) (hscale : 0 < scale) (hC : 0 ≤ C)
    (hbound : ∀ x, scale ^ 2 * ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator S m x‖) :
    ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤
      (Real.sqrt (Fintype.card V) * C) / scale ^ 2 := by
  have hh := EuclideanInverse.stability_inverse_upper S a z m hS hz hm hsol
    (C / scale ^ 2) (by positivity) (fun x => by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hscale)).mpr
      nlinarith [hbound x])
  simpa only [mul_div_assoc] using hh

/-- Original symmetric bulk proposition, in the paper's Euclidean inverse norm. -/
theorem symmetric_strip_inverse
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (b M c s P R H : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hs : 0 < s) (hP : 0 < P) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsup : ∀ i j, S i j ≠ 0 → s ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
      (hz : 0 < z.im), z.im ≤ H → 0 < rho → rho ≤ P →
      (∀ i, c * rho ≤ (m i).im) → (∀ i, (m i).im ≤ rho) →
      (∀ i, b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤
        C / (rho * ‖fun i => z - (a i : ℂ)‖) ^ 2 := by
  obtain ⟨C0, hC0, hbound⟩ := BulkStrip.symmetric_strip_bound external S hS hcS hsymm
    b M c s P R H hb hM hc hs hP hR hH hsup hrow
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine ⟨Real.sqrt (Fintype.card V) * C0, mul_pos (Real.sqrt_pos.mpr hd) hC0, ?_⟩
  intro a z m rho hm hsol hz hzH hr hrP hylo hyhi hlo hhi
  exact inverse_of_scaled_coercivity S a z m hS hz hm hsol _ C0
    (mul_pos hr (shift_norm_pos a z hz)) hC0.le
    (hbound a z m rho hm hsol hz.le hzH hr hrP hylo hyhi hlo hhi)

/-- Original stronger symmetric non-bipartite proposition in Euclidean norm. -/
theorem symmetric_nonbipartite_inverse
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (b M c s P : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hs : 0 < s) (hP : 0 < P) (hsup : ∀ i j, S i j ≠ 0 → s ≤ S i j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
      (hz : 0 < z.im), 0 < rho → rho ≤ P →
      (∀ i, c * rho ≤ (m i).im) → (∀ i, (m i).im ≤ rho) →
      (∀ i, b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤ C / rho ^ 2 := by
  obtain ⟨C0, hC0, hbound⟩ := BulkStrip.symmetric_nonbipartite_bound external S hS hcS hsymm hnb
    b M c s P hb hM hc hs hP hsup
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  refine ⟨Real.sqrt (Fintype.card V) * C0, mul_pos (Real.sqrt_pos.mpr hd) hC0, ?_⟩
  intro a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi
  exact inverse_of_scaled_coercivity S a z m hS hz hm hsol rho C0 hr hC0.le
    (hbound a z m rho hm hsol hz.le hr hrP hylo hyhi hlo hhi)

namespace NB
variable (G : BaseGraph V) [Fintype G.Edge]

theorem strip_inverse (external : BulkTorus.FiniteTorusErrorBound.{u})
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge) (hbase : StronglyConnected G.Adj)
    (b M c P B H : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c)
    (hP : 0 < P) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m)
      (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m) (hz : 0 < z.im),
      z.im ≤ H → 0 < rho → rho ≤ P →
      (∀ e, c * rho ≤ (m e).im) → (∀ e, (m e).im ≤ rho) →
      (∀ e, b ≤ ‖m e‖) → (∀ e, ‖m e‖ ≤ M) → (∀ y, ‖z - (a y : ℂ)‖ ≤ B) →
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol‖ ≤
        C / (rho * ‖fun y => z - (a y : ℂ)‖) ^ 2 := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨C0, hC0, hbound⟩ := BulkNBStrip.strip_bound G external hd root hbase b M c P B H hb hM hc hP hB hH
  have hd' : (0 : ℝ) < Fintype.card G.Edge := by exact_mod_cast Fintype.card_pos
  refine ⟨Real.sqrt (Fintype.card G.Edge) * C0, mul_pos (Real.sqrt_pos.mpr hd') hC0, ?_⟩
  intro a z m rho hm hsol hz hzH hr hrP hylo hyhi hlo hhi hshift
  exact inverse_of_scaled_coercivity G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol _ C0
    (mul_pos hr (shift_norm_pos a z hz)) hC0.le
    (hbound a z m rho hm hsol hz.le hzH hr hrP hylo hyhi hlo hhi hshift)

theorem nonbipartite_inverse (external : BulkTorus.FiniteTorusErrorBound.{u})
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge) (hbase : StronglyConnected G.Adj)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)
    (b M c P : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m)
      (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m) (hz : 0 < z.im),
      0 < rho → rho ≤ P →
      (∀ e, c * rho ≤ (m e).im) → (∀ e, (m e).im ≤ rho) →
      (∀ e, b ≤ ‖m e‖) → (∀ e, ‖m e‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol‖ ≤
        C / rho ^ 2 := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨C0, hC0, hbound⟩ := BulkNBNonbip.nonbipartite_strip_bound G external hd root hbase hnb
    b M c P hb hM hc hP
  have hd' : (0 : ℝ) < Fintype.card G.Edge := by exact_mod_cast Fintype.card_pos
  refine ⟨Real.sqrt (Fintype.card G.Edge) * C0, mul_pos (Real.sqrt_pos.mpr hd') hC0, ?_⟩
  intro a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi
  exact inverse_of_scaled_coercivity G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol rho C0 hr hC0.le
    (hbound a z m rho hm hsol hz.le hr hrP hylo hyhi hlo hhi)

end NB
end NonSymmetricDyson.Full.BulkEuclidean
