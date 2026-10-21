import Dyson.Full.BulkConnectivity
import Dyson.Full.MainBoundary
import Dyson.Model
import Dyson.InteriorStability
import Dyson.IrreduciblePositivity

/-! Exact finite-index representation of the actual graph model.  Directed
connectivity plus an outgoing edge yields positive powers with positive
exponent, including the return-to-self case.  Reindexing preserves equations,
residuals, norms, and canonical boundary support. -/
noncomputable section
open scoped BigOperators Topology
namespace NonSymmetricDyson.Full.BulkMatrixBridge

universe u v
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]

def matrix (e : V ≃ W) (S : Matrix V V ℝ) : Matrix W W ℝ :=
  fun i j => S (e.symm i) (e.symm j)

def vector (e : V ≃ W) {K : Type*} (v : V → K) : W → K := fun i => v (e.symm i)

def family (e : V ≃ W) (m : ℂ → V → ℂ) : ℂ → W → ℂ := fun z => vector e (m z)

@[simp] theorem vector_apply (e : V ≃ W) {K : Type*} (v : V → K) (i : W) :
    vector e v i = v (e.symm i) := rfl

@[simp] theorem vector_apply_image (e : V ≃ W) {K : Type*} (v : V → K) (i : V) :
    vector e v (e i) = v i := by simp [vector]

@[simp] theorem vector_symm (e : V ≃ W) {K : Type*} (v : V → K) :
    vector e.symm (vector e v) = v := by funext i; simp [vector]

theorem power_nonnegative [DecidableEq V] (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∀ k i j, 0 ≤ (S ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split <;> norm_num
  | succ k ih =>
      intro i j
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (hS i t) (ih t j))

/-- Every actual positive-support walk produces a positive power entry. -/
theorem positive_power_of_walk [DecidableEq V]
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    {i j : V} (p : Resonance.Walk (fun x y => 0 < S x y) i j) :
    ∃ k : ℕ, 0 < (S ^ k) i j := by
  induction p with
  | nil i => exact ⟨0, by simp⟩
  | @cons i t j hit p ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_pos' (fun x _ => mul_nonneg (hS i x) (power_nonnegative S hS k x j))
        ⟨t, Finset.mem_univ t, mul_pos hit hk⟩

/-- Outgoing edges ensure a strictly positive exponent even on the diagonal;
strong connectivity alone would permit the empty walk. -/
theorem positive_power_connected [DecidableEq V]
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hout : ∀ i, ∃ t, 0 < S i t) :
    ∀ i j, ∃ k : ℕ, 1 ≤ k ∧ 0 < (S ^ k) i j := by
  intro i j
  obtain ⟨t, hit⟩ := hout i
  obtain ⟨p⟩ := hc t j
  obtain ⟨k, hk⟩ := positive_power_of_walk S hS p
  refine ⟨k + 1, by omega, ?_⟩
  rw [pow_succ', Matrix.mul_apply]
  exact Finset.sum_pos' (fun x _ => mul_nonneg (hS i x) (power_nonnegative S hS k x j))
    ⟨t, Finset.mem_univ t, mul_pos hit hk⟩

theorem reindex_walk (e : V ≃ W) (R : V → V → Prop) {i j : V}
    (p : Resonance.Walk R i j) :
    Nonempty (Resonance.Walk (fun x y => R (e.symm x) (e.symm y)) (e i) (e j)) := by
  induction p with
  | nil i => exact ⟨Resonance.Walk.nil _⟩
  | cons h p ih =>
      obtain ⟨q⟩ := ih
      exact ⟨Resonance.Walk.cons (by simpa using h) q⟩

theorem matrix_stronglyConnected (e : V ≃ W) (S : Matrix V V ℝ)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j)) :
    Resonance.StronglyConnected (fun i j => 0 < matrix e S i j) := by
  intro i j
  obtain ⟨p⟩ := hc (e.symm i) (e.symm j)
  simpa [matrix] using reindex_walk e (fun x y => 0 < S x y) p

theorem fin_irreducible (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hout : ∀ i, ∃ j, 0 < S i j) :
    Manuscript.PositivityCorrection.Irreducible (matrix (Fintype.equivFin V) S) := by
  apply positive_power_connected _ (fun i j => hS _ _) (matrix_stronglyConnected _ S hc)
  intro i
  obtain ⟨j, hj⟩ := hout ((Fintype.equivFin V).symm i)
  exact ⟨Fintype.equivFin V j, by simpa [matrix] using hj⟩

theorem action_reindex (e : V ≃ W) (S : Matrix V V ℝ) (v : V → ℂ) :
    Model.action (matrix e S) (vector e v) = vector e (Model.action S v) := by
  funext i
  simp only [Model.action_apply, matrix, vector]
  exact e.symm.sum_comp (fun j => (S (e.symm i) j : ℂ) * v j)

theorem residual_reindex (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (g : V → ℂ) :
    Model.residual (matrix e S) (vector e a) z (vector e g) = vector e (Model.residual S a z g) := by
  funext i
  simp only [Model.residual, action_reindex, vector]

theorem upper_reindex_iff (e : V ≃ W) (m : V → ℂ) :
    BasicEstimates.IsUpperSolution (vector e m) ↔ BasicEstimates.IsUpperSolution m := by
  constructor
  · intro h i
    simpa using h (e i)
  · intro h i
    exact h (e.symm i)

theorem dyson_reindex_iff (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ) :
    BasicEstimates.IsDysonSolution (matrix e S) (vector e a) z (vector e m) ↔
      BasicEstimates.IsDysonSolution S a z m := by
  rw [← Model.residual_zero_iff, residual_reindex, ← Model.residual_zero_iff]
  constructor
  · intro h
    funext i
    have hh := congrFun h (e i)
    simpa using hh
  · intro h
    rw [h]
    rfl

theorem norm_vector (e : V ≃ W) (v : V → ℂ) : ‖vector e v‖ = ‖v‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun i => norm_le_pi_norm v (e.symm i))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (vector e v))).mpr
    intro i
    simpa using norm_le_pi_norm (vector e v) (e i)

@[simp] theorem vector_sub (e : V ≃ W) (v w : V → ℂ) :
    vector e (v - w) = vector e v - vector e w := rfl

def reindexIsometry (e : V ≃ W) : (V → ℂ) ≃ₗᵢ[ℂ] (W → ℂ) where
  toLinearEquiv := LinearEquiv.piCongrLeft' ℂ (fun _ : V => ℂ) e
  norm_map' := norm_vector e

theorem continuous_family_reindex {X : Type*} [TopologicalSpace X]
    (e : V ≃ W) (m : X → V → ℂ) {K : Set X} (hm : ContinuousOn m K) :
    ContinuousOn (fun x => vector e (m x)) K :=
  (reindexIsometry e).continuous.comp_continuousOn hm

theorem stability_reindex (e : V ≃ W) (S : Matrix V V ℝ) (m u : V → ℂ) :
    InteriorStability.stabilityOperator (matrix e S) (vector e m) (vector e u) =
      vector e (InteriorStability.stabilityOperator S m u) := by
  funext i
  have hh := congrFun (action_reindex e S u) i
  simpa [InteriorStability.stabilityOperator, Model.action_apply, vector, matrix] using
    congrArg (fun x : ℂ => u (e.symm i) - m (e.symm i)^2 * x) hh

@[simp] theorem boundary_reindex (e : V ≃ W) (m : ℂ → V → ℂ) (z : ℂ) :
    Boundary.boundaryVector (family e m) z = vector e (Boundary.boundaryVector m z) := rfl

theorem singularUnion_reindex (e : V ≃ W) (m : ℂ → V → ℂ) :
    Boundary.singularUnion (family e m) = Boundary.singularUnion m := by
  ext x
  simp only [Boundary.singularUnion, Set.mem_iUnion, family, vector]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa using hi⟩

theorem regularSupport_reindex (e : V ≃ W) (m : ℂ → V → ℂ) (i : V) :
    Boundary.regularSupport (family e m) (e i) = Boundary.regularSupport m i := by
  ext x
  simp [Boundary.regularSupport, singularUnion_reindex, vector]

@[simp] theorem norm_vector_sub (e : V ≃ W) (v w : V → ℂ) :
    ‖vector e v - vector e w‖ = ‖v - w‖ := by
  rw [← vector_sub, norm_vector]

@[simp] theorem norm_residual_reindex (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ)
    (z : ℂ) (g : V → ℂ) :
    ‖Model.residual (matrix e S) (vector e a) z (vector e g)‖ = ‖Model.residual S a z g‖ := by
  rw [residual_reindex, norm_vector]

namespace NB
variable {X : Type*} [Fintype X] (G : Nonbacktracking.BaseGraph X) [Fintype G.Edge]

theorem outgoing (hd : BulkGraph.NB.HasThreeNeighbors G) : ∀ e, ∃ f, 0 < G.matrix e f := by
  classical
  intro e
  obtain ⟨x, hx, hxt, _⟩ := hd (G.head e) (G.tail e) (G.tail e)
  let f : G.Edge := ⟨(G.head e, x), hx⟩
  refine ⟨f, ?_⟩
  have hfollow : G.CanFollow e f := ⟨rfl, hxt⟩
  simp [Nonbacktracking.BaseGraph.matrix, hfollow]

theorem fin_matrix_irreducible (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : Resonance.StronglyConnected G.Adj) :
    Manuscript.PositivityCorrection.Irreducible (matrix (Fintype.equivFin G.Edge) G.matrix) := by
  have hpos : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
    funext i j
    exact propext (by
      classical
      by_cases h : G.CanFollow i j <;> simp [Nonbacktracking.BaseGraph.matrix, h])
  apply fin_irreducible G.matrix G.matrix_nonnegative ?_ (outgoing G hd)
  rw [hpos]
  exact BulkConnectivity.NB.stronglyConnected G hd hc

theorem fin_model_data (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : Resonance.StronglyConnected G.Adj) (root : G.Edge)
    (a : X → ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z)) :
    0 < Fintype.card G.Edge ∧
    Manuscript.PositivityCorrection.Nonnegative (matrix (Fintype.equivFin G.Edge) G.matrix) ∧
    Manuscript.PositivityCorrection.Irreducible (matrix (Fintype.equivFin G.Edge) G.matrix) ∧
    (∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (family (Fintype.equivFin G.Edge) m z)) ∧
    (∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution
      (matrix (Fintype.equivFin G.Edge) G.matrix) (vector (Fintype.equivFin G.Edge) (G.terminalShift a)) z
      (family (Fintype.equivFin G.Edge) m z)) := by
  letI : Nonempty G.Edge := ⟨root⟩
  refine ⟨Fintype.card_pos, fun _ _ => G.matrix_nonnegative _ _, fin_matrix_irreducible G hd hc, ?_, ?_⟩
  · intro z hz
    exact (upper_reindex_iff _ _).mpr (hupper z hz)
  · intro z hz
    exact (dyson_reindex_iff _ _ _ _ _).mpr (heq z hz)

end NB
end NonSymmetricDyson.Full.BulkMatrixBridge
