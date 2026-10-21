import Dyson.Full.BulkKernel
import Dyson.Full.BulkDyson
import Dyson.Full.BulkTransfer

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkBoundary
open Resonance
variable {V : Type*} [Fintype V]

def boundaryMarkov (S : Matrix V V ℝ) (m : V → ℂ) : Matrix V V ℝ :=
  fun i j => ‖m i‖ ^ 2 * S i j * (m j).im / (m i).im

theorem boundaryMarkov_nonnegative (S : Matrix V V ℝ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hm : BasicEstimates.IsUpperSolution m) :
    ∀ i j, 0 ≤ boundaryMarkov S m i j := by
  intro i j
  exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hS i j)) (hm j).le) (hm i).le

theorem boundaryMarkov_support (S : Matrix V V ℝ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hm : BasicEstimates.IsUpperSolution m) (i j : V) :
    0 < boundaryMarkov S m i j ↔ S i j ≠ 0 := by
  have hn : 0 < ‖m i‖ := norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)
  unfold boundaryMarkov
  rw [div_pos_iff_of_pos_right (hm i), mul_pos_iff_of_pos_right (hm j),
    mul_pos_iff_of_pos_left (sq_pos_of_pos hn)]
  exact lt_iff_le_and_ne.trans (by simp [hS i j, ne_comm])

theorem boundaryMarkov_row_sum (S : Matrix V V ℝ) (a : V → ℝ) (tau : ℝ)
    (m : V → ℂ) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a (tau : ℂ) m) (i : V) :
    ∑ j, boundaryMarkov S m i j = 1 := by
  have hh := BasicEstimates.weighted_imaginary_part_identity hm hsol i
  simp only [Complex.ofReal_im, zero_add, Complex.normSq_eq_norm_sq] at hh
  simp only [boundaryMarkov, ← Finset.sum_div]
  have he : (∑ j, ‖m i‖ ^ 2 * S i j * (m j).im) = (m i).im := by
    rw [hh, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, div_self (ne_of_gt (hm i))]

theorem boundary_conjugation (S : Matrix V V ℝ) (m : V → ℂ)
    (hm : BasicEstimates.IsUpperSolution m) (x : V → ℂ) :
    MarkovStability.phaseMarkovOperator (boundaryMarkov S m)
      (fun i => (BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm) i : ℂ)) 1
      (fun i => x i / ((m i).im : ℂ)) =
    fun i => ((BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm) i : ℂ) /
      ((m i).im : ℂ)) * InteriorStability.stabilityOperator S m x i := by
  funext i
  have hi : ((m i).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))
  have hterm (j : V) : ((boundaryMarkov S m i j : ℝ) : ℂ) *
      (x j / ((m j).im : ℂ)) =
        (‖m i‖ : ℂ) ^ 2 / ((m i).im : ℂ) * ((S i j : ℂ) * x j) := by
    have hj : ((m j).im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm j))
    simp only [boundaryMarkov, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    field_simp
  simp only [MarkovStability.phaseMarkovOperator_apply, hterm, Complex.ofReal_one,
    one_mul, ← Finset.mul_sum, InteriorStability.stabilityOperator_apply]
  field_simp
  rw [← BulkTransfer.dysonPhase_identity m (BasicEstimates.component_ne_zero hm) i]
  ring

/-- The physical boundary solution itself supplies the stochastic weight;
no Perron theorem or arbitrary eigenvector is needed here. -/
theorem resonance_of_dyson_kernel [Nonempty V]
    (S : Matrix V V ℝ) (a : V → ℝ) (tau : ℝ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a (tau : ℂ) m)
    (x : V → ℂ) (hx : x ≠ 0) (hker : InteriorStability.stabilityOperator S m x = 0) :
    CycleResonant (fun i j => S i j ≠ 0)
      (fun i => (BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i)) ^ 2) := by
  let Q := boundaryMarkov S m
  let u := BulkTransfer.dysonPhase m (BasicEstimates.component_ne_zero hm)
  let v : V → ℂ := fun i => x i / ((m i).im : ℂ)
  have hv : v ≠ 0 := by
    intro hv0
    apply hx
    funext i
    have hi := congrFun hv0 i
    change x i / ((m i).im : ℂ) = 0 at hi
    exact (div_eq_zero_iff.mp hi).resolve_right
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i)))
  have hQeq : (fun i j => 0 < Q i j) = (fun i j => S i j ≠ 0) := by
    funext i j
    exact propext (boundaryMarkov_support S m hS hm i j)
  have hcQ : StronglyConnected (fun i j => 0 < Q i j) := by rw [hQeq]; exact hc
  have hvker : MarkovStability.phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 v = 0 := by
    rw [show v = (fun i => x i / ((m i).im : ℂ)) from rfl]
    have hh := boundary_conjugation S m hm x
    rw [hker] at hh
    simpa [Q, u] using hh
  have hres := BulkKernel.resonance_of_kernel Q (boundaryMarkov_nonnegative S m hS hm)
    (boundaryMarkov_row_sum S a tau m hm hsol) hcQ u v hv hvker
  rw [hQeq] at hres
  apply (BulkKernel.cycleResonant_inverse_iff _ _).mp
  change CycleResonant (fun i j => S i j ≠ 0)
    (fun i => ((BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i))⁻¹) ^ 2) at hres
  simpa only [inv_pow] using hres

/-- Actual invertibility at every nonexceptional positive-density symmetric
boundary point. The only possible obstruction is constant potential equal to
the energy on a bipartite support graph. -/
theorem symmetric_boundary_bijective [Nonempty V]
    (S : Matrix V V ℝ) (a : V → ℝ) (tau : ℝ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a (tau : ℂ) m)
    (hexception : ¬ ((∀ i, a i = tau) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)) :
    Function.Bijective (InteriorStability.stabilityOperator S m) := by
  have hk : ∀ x, InteriorStability.stabilityOperator S m x = 0 → x = 0 := by
    intro x hx
    by_contra hn
    have hr := resonance_of_dyson_kernel S a tau m hS hc hm hsol x hn hx
    apply hexception
    exact ⟨BulkDyson.symmetric_resonance_forces_constant_potential S a tau m hsymm hm hsol hr,
      BulkDyson.symmetric_physical_resonance_bipartite S m (Classical.arbitrary V) hsymm hc hm hr⟩
  have hi : Function.Injective (InteriorStability.stabilityOperator S m) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hk
    rw [map_sub, he, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem square_norm_of_real (w : ℂ) (hw : w.im = 0) :
    w ^ 2 = (‖w‖ : ℂ) ^ 2 := by
  have he : w = (w.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hw
  rw [he, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, sq_abs]

theorem squared_phase_of_real_product (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hreal : (x * y).im = 0) :
    (BulkPhase.normalize x hx) ^ 2 * (BulkPhase.normalize y hy) ^ 2 = 1 := by
  apply Circle.coe_injective
  change (x / (‖x‖ : ℂ)) ^ 2 * (y / (‖y‖ : ℂ)) ^ 2 = 1
  have hxn : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hyn : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hs := square_norm_of_real (x * y) hreal
  rw [norm_mul, Complex.ofReal_mul] at hs
  field_simp
  linear_combination hs

namespace NB
open Nonbacktracking
variable (G : BaseGraph V) [Fintype G.Edge]

/-- The physical vertex denominators descend the NB resonance to a symmetric
base-graph resonance, which forces the base graph to be bipartite. -/
theorem resonance_forces_bipartite
    (a : V → ℝ) (tau : ℝ) (m : G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (tau : ℂ) m)
    (hres : CycleResonant G.CanFollow
      (fun e => (BulkPhase.normalize (m e) (BasicEstimates.component_ne_zero hm e)) ^ 2)) :
    ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part := by
  let phase (e : G.Edge) :=
    (BulkPhase.normalize (m e) (BasicEstimates.component_ne_zero hm e)) ^ 2
  have hconn := BulkConnectivity.NB.stronglyConnected G hd hbase
  obtain ⟨omega, homega⟩ := (BulkGraph.NB.resonance_iff_vertex_potentials
    G hd root hconn phase).mp hres
  let H := BulkDyson.NB.vertexDenominator G a tau m
  have hH (y : V) : 0 < (H y).im := by
    obtain ⟨x, hxy, _, _⟩ := hd y y y
    let e : G.Edge := ⟨(x,y), G.symm hxy⟩
    have hh := BulkDyson.NB.outgoingSum_im_pos G m hm e
    simpa [H, BulkDyson.NB.vertexDenominator, e, BaseGraph.head] using hh
  have hH0 (y : V) : H y ≠ 0 := by
    intro he
    have hh := hH y
    simpa [he] using hh
  let phi (y : V) := (BulkPhase.normalize (H y) (hH0 y)) ^ 2
  have hreal (e : G.Edge) : (m e * m (G.reverse e)).im = 0 :=
    BulkDyson.real_product_of_squared_phase _ _
      (BasicEstimates.component_ne_zero hm e) (BasicEstimates.component_ne_zero hm (G.reverse e))
      (BulkGraph.NB.resonant_reverse_product G hd root hconn phase hres e)
  have hp (e : G.Edge) : phi (G.head e) * phase e = 1 :=
    squared_phase_of_real_product (H (G.head e)) (m e) (hH0 _)
      (BasicEstimates.component_ne_zero hm e)
      (BulkDyson.NB.real_vertex_product G a tau m hm hsol hreal e)
  have hg : HasVertexGauge G.Adj phi := by
    refine ⟨omega, ?_⟩
    intro x y hxy
    let e : G.Edge := ⟨(x,y), hxy⟩
    have hh := hp (G.reverse e)
    change phi x * phase (G.reverse e) = 1 at hh
    calc
      phi x = (phi x * phase (G.reverse e)) * (phase (G.reverse e))⁻¹ := by simp [mul_assoc]
      _ = (phase (G.reverse e))⁻¹ := by rw [hh, one_mul]
      _ = (omega x)⁻¹ * omega y := by
        rw [homega]
        simp only [BaseGraph.reverse_tail, BaseGraph.reverse_head]
        change ((omega y)⁻¹ * omega x)⁻¹ = (omega x)⁻¹ * omega y
        simp
  apply BulkGraph.bipartition_of_nontrivial_resonance
    (fun _ _ h => G.symm h) hbase phi (cycleResonant_of_hasVertexGauge phi hg)
    (G.tail root)
  exact BulkDyson.phase_square_ne_one (H (G.tail root)) (hH _)

/-- Actual NB boundary invertibility outside exactly the constant-potential
bipartite exception, with no Perron or torus assumption. -/
theorem boundary_bijective
    (a : V → ℝ) (tau : ℝ) (m : G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (tau : ℂ) m)
    (hexception : ¬ ((∀ y, a y = tau) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)) :
    Function.Bijective (InteriorStability.stabilityOperator G.matrix m) := by
  letI : Nonempty G.Edge := ⟨root⟩
  have hconn := BulkConnectivity.NB.stronglyConnected G hd hbase
  have heq : (fun e f => G.matrix e f ≠ 0) = G.CanFollow := by
    funext e f
    apply propext
    by_cases h : G.CanFollow e f <;> simp [BaseGraph.matrix, h]
  have hcS : StronglyConnected (fun e f => G.matrix e f ≠ 0) := by rw [heq]; exact hconn
  have hk : ∀ x, InteriorStability.stabilityOperator G.matrix m x = 0 → x = 0 := by
    intro x hx
    by_contra hn
    have hr := resonance_of_dyson_kernel G.matrix (G.terminalShift a) tau m
      G.matrix_nonnegative hcS hm hsol x hn hx
    rw [heq] at hr
    apply hexception
    exact ⟨BulkDyson.NB.resonance_forces_constant_terminal_potential
        G a tau m hd root hconn hm hsol hr,
      resonance_forces_bipartite G a tau m hd root hbase hm hsol hr⟩
  have hi : Function.Injective (InteriorStability.stabilityOperator G.matrix m) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hk
    rw [map_sub, he, sub_self]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

end NB
end NonSymmetricDyson.Full.BulkBoundary
