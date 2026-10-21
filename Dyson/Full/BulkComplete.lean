import Dyson.Full.BulkInputs

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkComplete
universe u
open Resonance Nonbacktracking
variable {V : Type u} [Fintype V] [Nonempty V]

def rho (m : V → ℂ) : ℝ := ∑ i, (m i).im

theorem symmetric_bulk (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (M Z : ℝ) (hM : 0 < M) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : V → ℂ)
      (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
      (hz : 0 < z.im), ‖z‖ ≤ Z → (∀ i, ‖m i‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤
        C / (rho m * ‖fun i => z - (a i : ℂ)‖) ^ 2 := by
  obtain ⟨b,c,s,P,R,B,hb,hc,hs,hP,hR,hB,hsup,hrow,hdata⟩ :=
    BulkInputs.uniform_data S a hS hcS M Z hM hZ
  obtain ⟨C,hC,hbound⟩ := BulkEuclidean.symmetric_strip_inverse external S hS hcS hsymm
    b M c s P R Z hb hM hc hs hP hR hZ hsup hrow
  refine ⟨C,hC,?_⟩
  intro z m hm hsol hz hzN hnorm
  obtain ⟨hr,hrP,hylo,hyhi,hlo,_⟩ := hdata z m hm hsol hz.le hzN hnorm
  have hzZ : z.im ≤ Z := ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans hzN
  exact hbound a z m (rho m) hm hsol hz hzZ hr hrP hylo hyhi hlo hnorm

theorem symmetric_nonbipartite_bulk (external : BulkTorus.FiniteTorusErrorBound.{u})
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (M Z : ℝ) (hM : 0 < M) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : V → ℂ)
      (hm : BasicEstimates.IsUpperSolution m) (hsol : BasicEstimates.IsDysonSolution S a z m)
      (hz : 0 < z.im), ‖z‖ ≤ Z → (∀ i, ‖m i‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse S a z m hS hz hm hsol‖ ≤ C / rho m ^ 2 := by
  obtain ⟨b,c,s,P,R,B,hb,hc,hs,hP,hR,hB,hsup,hrow,hdata⟩ :=
    BulkInputs.uniform_data S a hS hcS M Z hM hZ
  obtain ⟨C,hC,hbound⟩ := BulkEuclidean.symmetric_nonbipartite_inverse external S hS hcS hsymm hnb
    b M c s P hb hM hc hs hP hsup
  refine ⟨C,hC,?_⟩
  intro z m hm hsol hz hzN hnorm
  obtain ⟨hr,hrP,hylo,hyhi,hlo,_⟩ := hdata z m hm hsol hz.le hzN hnorm
  exact hbound a z m (rho m) hm hsol hz hr hrP hylo hyhi hlo hnorm

namespace NB
variable (G : BaseGraph V) [Fintype G.Edge]

theorem bulk (external : BulkTorus.FiniteTorusErrorBound.{u})
    (a : V → ℝ) (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj) (M Z : ℝ) (hM : 0 < M) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : G.Edge → ℂ)
      (hm : BasicEstimates.IsUpperSolution m)
      (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
      (hz : 0 < z.im), ‖z‖ ≤ Z → (∀ e, ‖m e‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol‖ ≤
        C / ((∑ e, (m e).im) * ‖fun y => z - (a y : ℂ)‖) ^ 2 := by
  letI : Nonempty G.Edge := ⟨root⟩
  have hcS : StronglyConnected (fun e f => G.matrix e f ≠ 0) := by
    rw [BulkNBStrip.support_eq]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  obtain ⟨b,c,s,P,R,B,hb,hc,hs,hP,hR,hB,hsup,hrow,hdata⟩ :=
    BulkInputs.uniform_data G.matrix (G.terminalShift a) G.matrix_nonnegative hcS M Z hM hZ
  obtain ⟨C,hC,hbound⟩ := BulkEuclidean.NB.strip_inverse G external hd root hbase
    b M c P B Z hb hM hc hP hB hZ
  refine ⟨C,hC,?_⟩
  intro z m hm hsol hz hzN hnorm
  obtain ⟨hr,hrP,hylo,hyhi,hlo,hshift⟩ := hdata z m hm hsol hz.le hzN hnorm
  have hzZ : z.im ≤ Z := ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans hzN
  have hshiftV (y : V) : ‖z - (a y : ℂ)‖ ≤ B := by
    obtain ⟨x,hxy,_,_⟩ := hd y y y
    let e : G.Edge := ⟨(x,y),G.symm hxy⟩
    exact hshift e
  exact hbound a z m (∑ e, (m e).im) hm hsol hz hzZ hr hrP hylo hyhi hlo hnorm hshiftV

theorem nonbipartite_bulk (external : BulkTorus.FiniteTorusErrorBound.{u})
    (a : V → ℝ) (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)
    (M Z : ℝ) (hM : 0 < M) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : G.Edge → ℂ)
      (hm : BasicEstimates.IsUpperSolution m)
      (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
      (hz : 0 < z.im), ‖z‖ ≤ Z → (∀ e, ‖m e‖ ≤ M) →
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z m G.matrix_nonnegative hz hm hsol‖ ≤
        C / (∑ e, (m e).im) ^ 2 := by
  letI : Nonempty G.Edge := ⟨root⟩
  have hcS : StronglyConnected (fun e f => G.matrix e f ≠ 0) := by
    rw [BulkNBStrip.support_eq]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  obtain ⟨b,c,s,P,R,B,hb,hc,hs,hP,hR,hB,hsup,hrow,hdata⟩ :=
    BulkInputs.uniform_data G.matrix (G.terminalShift a) G.matrix_nonnegative hcS M Z hM hZ
  obtain ⟨C,hC,hbound⟩ := BulkEuclidean.NB.nonbipartite_inverse G external hd root hbase hnb
    b M c P hb hM hc hP
  refine ⟨C,hC,?_⟩
  intro z m hm hsol hz hzN hnorm
  obtain ⟨hr,hrP,hylo,hyhi,hlo,_⟩ := hdata z m hm hsol hz.le hzN hnorm
  exact hbound a z m (∑ e, (m e).im) hm hsol hz hr hrP hylo hyhi hlo hnorm

end NB
end NonSymmetricDyson.Full.BulkComplete
