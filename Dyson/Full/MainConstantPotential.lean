import Dyson.Full.MainLinearConstantExceptional

/-! Literal model theorems for an arbitrary constant potential. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.Exceptional
universe u
variable {V : Type u} [Fintype V]

/-- M6 exceptional case for symmetric support, in the original spectral
variable and for any compact regular strict-bulk energy set. -/
theorem main_theorem_six_symmetric_exceptional [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (a : ℝ) (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => a) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z - (a : ℂ)‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => a) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => a) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z - (a : ℂ)‖⁻¹ := by
  have hconn : Resonance.StronglyConnected (fun i j => S i j ≠ 0) := by
    have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
      funext i j
      exact propext (lt_iff_le_and_ne.trans (by simp [hS i j, ne_comm]))
    rwa [← he]
  apply canonical_constant_exceptional_strip algebraic puiseux external S hS hc a m hupper heq J hJ
    hregular hbulk ?_ (partitionSign part) (partitionSign_square part)
    (fun _ _ h => partitionSign_flip part hp h)
  intro E hE hEn
  apply BulkBoundary.symmetric_boundary_bijective S (fun _ => a) E
    (Boundary.boundaryVector m (E : ℂ)) hS hconn hsymm (hbulk E hE)
    (Boundary.family_boundary_equation algebraic puiseux S (fun _ => a) hS m hupper heq E
      (hregular E hE)).2.2
  rintro ⟨ha, _⟩
  exact hEn (ha (Classical.arbitrary V)).symm

namespace NB

/-- M6 exceptional case for a bipartite non-backtracking model, including
arbitrary constant potential and energy sets not containing that potential. -/
theorem main_theorem_six_exceptional
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (a : ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => a) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z - (a : ℂ)‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => a) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => a) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z - (a : ℂ)‖⁻¹ := by
  classical
  letI : Nonempty G.Edge := ⟨root⟩
  have hconn : Resonance.StronglyConnected (fun i j => 0 < G.matrix i j) := by
    have he : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
      funext i j
      exact propext (by by_cases h : G.CanFollow i j <;> simp [Nonbacktracking.BaseGraph.matrix, h])
    rw [he]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  apply canonical_constant_exceptional_strip algebraic puiseux external G.matrix G.matrix_nonnegative hconn
    a m hupper heq J hJ hregular hbulk ?_ (fun e => partitionSign part (G.head e))
    (fun e => partitionSign_square part (G.head e))
    (Nonlinear.NB.transition_sign_flip G _ (fun _ _ h => partitionSign_flip part hp h))
  intro E hE hEn
  apply BulkBoundary.NB.boundary_bijective G (fun _ => a) E (Boundary.boundaryVector m (E : ℂ))
    hd root hbase (hbulk E hE)
    (Boundary.family_boundary_equation algebraic puiseux G.matrix (fun _ => a)
      G.matrix_nonnegative m hupper heq E (hregular E hE)).2.2
  rintro ⟨ha, _⟩
  exact hEn (ha (G.head root)).symm

/-- M7(ii), in the original constant-potential variable.  Vertex values
are reconstructed with z-a, exactly as in the original vertex equation. -/
theorem main_theorem_seven_constant_balance [Nonempty V]
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (a : ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => a) z (m z))
    (hregular : a ∉ Boundary.singularUnion m)
    (hbulk : BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (a : ℂ))) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      ‖z - (a : ℂ)‖ ≤ r → 0 < z.im → ‖g - m z‖ ≤ c →
      (∀ y, z - (a : ℂ) + Nonlinear.NB.incidence G g y ≠ 0) ∧
      ‖g - m z‖ ≤ C * (‖Model.residual G.matrix (fun _ => a) z g‖ +
        ‖∑ y, partitionSign part y * (Nonlinear.NB.vertexValues G g (z - (a : ℂ)) y -
          Nonlinear.NB.vertexValues G (m z) (z - (a : ℂ)) y)‖) := by
  classical
  obtain ⟨hq, _, hsol₀, hlim, _⟩ := canonical_constant_origin_data algebraic puiseux G.matrix
    G.matrix_nonnegative a m hupper heq hregular hbulk
  have hconn : Resonance.StronglyConnected (fun i j => 0 < G.matrix i j) := by
    have he : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
      funext i j
      exact propext (by by_cases h : G.CanFollow i j <;> simp [Nonbacktracking.BaseGraph.matrix, h])
    rw [he]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  have hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y := by
    intro y
    obtain ⟨x, hxy, _, _⟩ := hd y y y
    exact ⟨⟨(y, x), hxy⟩, rfl⟩
  let n : ℂ → G.Edge → ℂ := fun w => m (w + (a : ℂ))
  have hneq : ∀ w : ℂ, 0 < w.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) w (n w) := by
    intro w hw
    simpa [n] using (SpectralShift.constant_dyson_shift G.matrix a (w + (a : ℂ)) _).mp
      (heq _ (by simpa using hw))
  obtain ⟨r,c,C,hr,hc,hC,hb⟩ := Nonlinear.NB.bipartite_nonlinear_balance_near_origin G external _
    (partitionSign part) n hconn hq (partitionSign_square part)
    (fun _ _ h => partitionSign_flip part hp h) hdegree hsol₀ hlim hneq
  refine ⟨r,c,C,hr,hc,hC,?_⟩
  intro z g hzr hz hclose
  have hh := hb (z - (a : ℂ)) g hzr (by simpa using hz) (by simpa [n] using hclose)
  have hres : Model.residual G.matrix (fun _ => 0) (z - (a : ℂ)) g =
      Model.residual G.matrix (fun _ => a) z g := by
    funext e
    simp only [Model.residual, Complex.ofReal_zero, sub_zero]
  simpa only [n, sub_add_cancel, hres] using hh

end NB
end NonSymmetricDyson.Full.Exceptional
