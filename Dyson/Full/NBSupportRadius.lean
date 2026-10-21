import Dyson.Full.BulkConnectivity
import Dyson.Full.Foundations

/-! The maximum-degree support specialization used before the seventh theorem.
The degree is the number of oriented edges leaving a vertex, equal to the usual
neighbor count for the finite simple base graph. No analytic input beyond M1 is
introduced here. -/

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace NonSymmetricDyson.Full.NBSupportRadius
open Nonbacktracking
variable {V : Type*} [Fintype V] (G : BaseGraph V)

def degree (x : V) : ℕ := (Finset.univ.filter (fun e : G.Edge => G.tail e = x)).card

def maxDegree : ℕ := Finset.univ.sup (degree G)

theorem degree_eq_neighbor_count (x : V) :
    degree G x = (Finset.univ.filter (G.Adj x)).card := by
  apply Finset.card_bij (fun e _ => G.head e)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact he ▸ e.property
  · intro e he f hf hef
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he hf
    apply Subtype.ext
    exact Prod.ext (he.trans hf.symm) hef
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ⟨⟨(x,y),hy⟩, by simp [BaseGraph.tail], rfl⟩

theorem degree_le_maxDegree (x : V) : degree G x ≤ maxDegree G :=
  Finset.le_sup (f := degree G) (Finset.mem_univ x)

theorem head_degree_pos (e : G.Edge) : 0 < degree G (G.head e) := by
  apply Finset.card_pos.mpr
  exact ⟨G.reverse e, by simp⟩

theorem rowSum_eq_degree_sub_one (e : G.Edge) :
    (∑ f, G.matrix e f) = (degree G (G.head e) : ℝ) - 1 := by
  have h : (∑ f, G.matrix e f) = ((BulkConnectivity.NB.successors G e).card : ℝ) := by
    simp [BaseGraph.matrix, BulkConnectivity.NB.successors, Finset.sum_boole]
  rw [h, BulkConnectivity.NB.successors_card]
  change (((degree G (G.head e) - 1 : ℕ) : ℝ)) = _
  rw [Nat.cast_sub (head_degree_pos G e), Nat.cast_one]

theorem rowSum_le_maxDegree (e : G.Edge) :
    (∑ f, G.matrix e f) ≤ (maxDegree G : ℝ) - 1 := by
  rw [rowSum_eq_degree_sub_one]
  exact sub_le_sub_right (by exact_mod_cast degree_le_maxDegree G (G.head e)) 1

variable [Nonempty G.Edge]

theorem maxDegree_pos : 0 < maxDegree G := by
  let e : G.Edge := Classical.arbitrary G.Edge
  exact lt_of_lt_of_le (head_degree_pos G e) (degree_le_maxDegree G _)

theorem maxRowSum_le : Foundations.maxRowSum G.matrix ≤ (maxDegree G : ℝ) - 1 := by
  have hd : (1 : ℝ) ≤ maxDegree G := by exact_mod_cast maxDegree_pos G
  apply (pi_norm_le_iff_of_nonneg (by linarith : (0 : ℝ) ≤ (maxDegree G : ℝ) - 1)).mpr
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun f _ => G.matrix_nonnegative e f))]
  exact rowSum_le_maxDegree G e

theorem supportRadius_le :
    Foundations.supportRadius G.matrix (fun _ => 0) ≤
      2 * Real.sqrt ((maxDegree G : ℝ) - 1) := by
  change ‖(0 : G.Edge → ℝ)‖ + 2 * Real.sqrt (Foundations.maxRowSum G.matrix) ≤ _
  rw [norm_zero, zero_add]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (maxRowSum_le G)) (by norm_num)

theorem sqrt_maxDegree_sub_one_lt :
    Real.sqrt ((maxDegree G : ℝ) - 1) < (maxDegree G : ℝ) := by
  have hd : (1 : ℝ) ≤ maxDegree G := by exact_mod_cast maxDegree_pos G
  apply (Real.sqrt_lt (by linarith) (by linarith : (0 : ℝ) ≤ maxDegree G)).mpr
  nlinarith [sq_nonneg ((maxDegree G : ℝ) - 1)]

theorem supportRadius_lt :
    Foundations.supportRadius G.matrix (fun _ => 0) < 2 * (maxDegree G : ℝ) :=
  (supportRadius_le G).trans_lt (mul_lt_mul_of_pos_left (sqrt_maxDegree_sub_one_lt G) (by norm_num))

/-- The full spectral measure is supported in the interval used for M7. -/
theorem measure_support_maxDegree (μ : G.Edge → Measure ℝ)
    (hsupport : ∀ e, μ e (Set.Icc
      (-(Foundations.supportRadius G.matrix (fun _ => 0)))
      (Foundations.supportRadius G.matrix (fun _ => 0)))ᶜ = 0) :
    ∀ e, μ e (Set.Icc (-(2 * (maxDegree G : ℝ))) (2 * (maxDegree G : ℝ)))ᶜ = 0 := by
  intro e
  apply measure_mono_null (Set.compl_subset_compl.mpr ?_) (hsupport e)
  exact Set.Icc_subset_Icc (neg_le_neg (supportRadius_lt G).le) (supportRadius_lt G).le

/-- Actual canonical Dyson measures, with the maximum-degree support bound. -/
theorem canonical_measures_maxDegree
    (external : Foundations.ExternalStieltjesTheory G.Edge) :
    ∃ μ : G.Edge → Measure ℝ, ∀ e,
      IsProbabilityMeasure (μ e) ∧
      Foundations.Represents (fun z => GlobalWellPosedness.solution G.matrix
        (fun _ => 0) G.matrix_nonnegative z e) (μ e) ∧
      μ e (Set.Icc (-(2 * (maxDegree G : ℝ))) (2 * (maxDegree G : ℝ)))ᶜ = 0 := by
  obtain ⟨_, _, _, μ, hμ⟩ := Foundations.main_theorem_one_max_norm external
    (fun _ => 0) G.matrix_nonnegative
  have hs := measure_support_maxDegree G μ (fun e => (hμ e).2.2.1)
  exact ⟨μ, fun e => ⟨(hμ e).1, (hμ e).2.1, hs e⟩⟩

end NonSymmetricDyson.Full.NBSupportRadius
