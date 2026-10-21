import Dyson.Paper.BulkGraph
import Dyson.Full.BulkComplete
import Dyson.Full.RoughLinear
import Dyson.Full.BoundaryBounds

/-! Exact paper-facing forms of the three quantitative bulk propositions.
The extra proof parameters are universally quantified external mathematics,
not model-specific stability conclusions. -/
noncomputable section
open scoped BigOperators
open Set
namespace NonSymmetricDyson.Paper.BulkStability
open Full Resonance
universe u

def inverseNorm {V : Type*} [Fintype V] (S : Matrix V V ℝ) (a : V → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (z : ℂ) (hz : 0 < z.im) : ℝ :=
  ‖EuclideanInverse.stabilityInverse S a z (GlobalWellPosedness.solution S a hS z) hS hz
    (GlobalWellPosedness.solution_upper a hS hz)
    (GlobalWellPosedness.solution_equation a hS hz)‖

/-- `pro.simple-bound-stability`, on the full original closed-interval strip. -/
theorem simple_bound {n : ℕ} (hn : 0 < n)
    (external : Foundations.ExternalStieltjesTheory (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (I : Set ℝ) (_hclosed : IsClosed I) (_hinterval : OrdConnected I)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i,
      ‖GlobalWellPosedness.solution S a hS z i‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ I → ∀ hz : 0 < z.im,
      inverseNorm S a hS z hz ≤ C * (1 + z.im⁻¹) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨_,_,_,μ,hμ⟩ := Foundations.main_theorem_one_max_norm external a hS
  obtain ⟨b,B,β,hb,hB,_,hdata⟩ := Boundary.family_interior_global_bounds hn S a hS hirr
    (GlobalWellPosedness.solution S a hS)
    (fun z hz => GlobalWellPosedness.solution_upper a hS hz)
    (fun z hz => GlobalWellPosedness.solution_equation a hS hz)
    μ (fun i => (hμ i).1) (fun i => (hμ i).2.1) (Foundations.supportRadius S a)
    (by unfold Foundations.supportRadius; positivity) (fun i => (hμ i).2.2.1) I M hM hbound
  let R : ℝ := ‖fun i => ∑ j, S i j‖
  have hrow (i : Fin n) : ∑ j, S i j ≤ R :=
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  obtain ⟨C,hC,hh⟩ := Linear.rough_inverse_bound_of_scaled_components S a hS b B R hb hB
    (norm_nonneg _) hrow
  refine ⟨C,hC,?_⟩
  intro z hzI hz
  apply hh z _ hz (GlobalWellPosedness.solution_upper a hS hz)
    (GlobalWellPosedness.solution_equation a hS hz)
  · intro i
    have h := ((div_le_iff₀ (by positivity : 0 < 1+‖z‖)).mp ((hdata z hzI hz).1 i).1)
    simpa [mul_comm] using h
  · intro i
    have h := ((le_div_iff₀ (by positivity : 0 < 1+‖z‖)).mp ((hdata z hzI hz).1 i).2)
    simpa [mul_comm] using h

/-- `prop.bulk-stability-symmetric`, retaining actual matrix symmetry and
both original bounds. The bracket is the sum, as defined in the manuscript. -/
theorem symmetric_bulk {n : ℕ} (hn : 0 < n)
    (basis : Paper.BulkTorus.IntegerRowBasis.{0}) (geometry : Paper.BulkTorus.CircleMetricFacts)
    (characters : Paper.BulkTorus.ContinuousCharacterClassification.{0})
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j, S i j = S j i)
    (I : Set ℝ) (_hclosed : IsClosed I) (_hinterval : OrdConnected I)
    (sigma M : ℝ) (hsigma : 0 ≤ sigma) (hM : 0 < M) (_hI : I ⊆ Icc (-sigma) sigma)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i,
      ‖GlobalWellPosedness.solution S a hS z i‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ I → ∀ hz : 0 < z.im, ‖z‖ ≤ 2*sigma →
      inverseNorm S a hS z hz ≤
        C / ((∑ i, (GlobalWellPosedness.solution S a hS z i).im) *
          ‖fun i => z-(a i : ℂ)‖)^2 := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hc : StronglyConnected (fun i j => S i j ≠ 0) := by
    have h := Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr
    have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
      funext i j
      exact propext (lt_iff_le_and_ne.trans (by simp [hS i j,ne_comm]))
    rwa [he] at h
  obtain ⟨C,hC,hh⟩ := Full.BulkComplete.symmetric_bulk
    (Paper.BulkTorus.finite_torus_error_bound basis geometry characters) S a hS hc
    (fun i j h => by rwa [hsym j i]) M (2*sigma) hM (by positivity)
  exact ⟨C,hC,fun z hzI hz hzN => hh z _ (GlobalWellPosedness.solution_upper a hS hz)
    (GlobalWellPosedness.solution_equation a hS hz) hz hzN (hbound z hzI hz)⟩

theorem symmetric_nonbipartite_bulk {n : ℕ} (hn : 0 < n)
    (basis : Paper.BulkTorus.IntegerRowBasis.{0}) (geometry : Paper.BulkTorus.CircleMetricFacts)
    (characters : Paper.BulkTorus.ContinuousCharacterClassification.{0})
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j, S i j = S j i)
    (hnb : ¬∃ part : Set (Fin n), Full.BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (I : Set ℝ) (_hclosed : IsClosed I) (_hinterval : OrdConnected I)
    (sigma M : ℝ) (hsigma : 0 ≤ sigma) (hM : 0 < M) (_hI : I ⊆ Icc (-sigma) sigma)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i,
      ‖GlobalWellPosedness.solution S a hS z i‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ I → ∀ hz : 0 < z.im, ‖z‖ ≤ 2*sigma →
      inverseNorm S a hS z hz ≤ C / (∑ i, (GlobalWellPosedness.solution S a hS z i).im)^2 := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hc : StronglyConnected (fun i j => S i j ≠ 0) := by
    have h := Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr
    have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
      funext i j
      exact propext (lt_iff_le_and_ne.trans (by simp [hS i j,ne_comm]))
    rwa [he] at h
  obtain ⟨C,hC,hh⟩ := Full.BulkComplete.symmetric_nonbipartite_bulk
    (Paper.BulkTorus.finite_torus_error_bound basis geometry characters) S a hS hc
    (fun i j h => by rwa [hsym j i]) hnb M (2*sigma) hM (by positivity)
  exact ⟨C,hC,fun z hzI hz hzN => hh z _ (GlobalWellPosedness.solution_upper a hS hz)
    (GlobalWellPosedness.solution_equation a hS hz) hz hzN (hbound z hzI hz)⟩

namespace NB
variable {V : Type u} [Fintype V] [Nonempty V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

/-- `pro.bulk-stability-NB`, with the original base-graph assumptions. -/
theorem bulk
    (basis : Paper.BulkTorus.IntegerRowBasis.{u}) (geometry : Paper.BulkTorus.CircleMetricFacts)
    (characters : Paper.BulkTorus.ContinuousCharacterClassification.{u})
    (root : G.Edge) (hd : ∀ y, 3 ≤ Full.BulkGraph.NB.degree G y)
    (hc : StronglyConnected G.Adj) (a : V → ℝ)
    (I : Set ℝ) (_hclosed : IsClosed I) (_hinterval : OrdConnected I)
    (sigma M : ℝ) (hsigma : 0 ≤ sigma) (hM : 0 < M) (_hI : I ⊆ Icc (-sigma) sigma)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ e,
      ‖GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative z e‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ I → ∀ hz : 0 < z.im, ‖z‖ ≤ 2*sigma →
      inverseNorm G.matrix (G.terminalShift a) G.matrix_nonnegative z hz ≤
        C / ((∑ e, (GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative z e).im) *
          ‖fun y => z-(a y : ℂ)‖)^2 := by
  obtain ⟨C,hC,hh⟩ := Full.BulkComplete.NB.bulk G
    (Paper.BulkTorus.finite_torus_error_bound basis geometry characters) a
    (Full.BulkGraph.NB.hasThreeNeighbors_of_degree G hd) root hc M (2*sigma) hM (by positivity)
  exact ⟨C,hC,fun z hzI hz hzN => hh z _ (GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) hz hzN (hbound z hzI hz)⟩

theorem nonbipartite_bulk
    (basis : Paper.BulkTorus.IntegerRowBasis.{u}) (geometry : Paper.BulkTorus.CircleMetricFacts)
    (characters : Paper.BulkTorus.ContinuousCharacterClassification.{u})
    (root : G.Edge) (hd : ∀ y, 3 ≤ Full.BulkGraph.NB.degree G y)
    (hc : StronglyConnected G.Adj) (a : V → ℝ)
    (hnb : ¬∃ part : Set V, Full.BulkGraph.IsBipartition (E := G.Adj) part)
    (I : Set ℝ) (_hclosed : IsClosed I) (_hinterval : OrdConnected I)
    (sigma M : ℝ) (hsigma : 0 ≤ sigma) (hM : 0 < M) (_hI : I ⊆ Icc (-sigma) sigma)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ e,
      ‖GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative z e‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ I → ∀ hz : 0 < z.im, ‖z‖ ≤ 2*sigma →
      inverseNorm G.matrix (G.terminalShift a) G.matrix_nonnegative z hz ≤
        C / (∑ e, (GlobalWellPosedness.solution G.matrix (G.terminalShift a) G.matrix_nonnegative z e).im)^2 := by
  obtain ⟨C,hC,hh⟩ := Full.BulkComplete.NB.nonbipartite_bulk G
    (Paper.BulkTorus.finite_torus_error_bound basis geometry characters) a
    (Full.BulkGraph.NB.hasThreeNeighbors_of_degree G hd) root hc hnb M (2*sigma) hM (by positivity)
  exact ⟨C,hC,fun z hzI hz hzN => hh z _ (GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz) hz hzN (hbound z hzI hz)⟩

end NB
end NonSymmetricDyson.Paper.BulkStability
