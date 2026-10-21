import Dyson.Full.Nonlinear
import Dyson.Full.NonlinearBalance
import Dyson.Nonbacktracking
import Dyson.Full.Foundations

/-! Equations and large-height repair used at the start of the original M7
proof, specialized to the exact zero-potential NB matrix. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.Nonlinear
open Full
variable {V : Type*} [Fintype V]
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

theorem bootstrap_exact_dyson_expansion (z : ℂ) (m g : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z m)
    (hg : ∀ i,g i ≠ 0) :
    DysonPaper.Algebra.stabilityAction m (Model.action G.matrix) (g-m) =
      fun i => m i^2*Model.residual G.matrix (fun _ => 0) z g i + (g i-m i)^2/g i :=
  Model.exact_residual_expansion G.matrix (fun _ => 0) z m g heq
    (BasicEstimates.component_ne_zero hm) hg

/-- The repaired large-height estimate has the exact coefficient 4/η².
No false uniform lower bound on the coordinates is used at infinite height. -/
theorem large_height_stability (z : ℂ) (m g : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z m)
    (hg : ∀ i,g i ≠ 0) (hclose : ‖g-m‖ ≤ 1)
    (hres : ‖Model.residual G.matrix (fun _ => 0) z g‖ ≤ 1)
    (hheight : 2*(Foundations.maxRowSum G.matrix+1) ≤ z.im) :
    ‖g-m‖ ≤ 4/z.im^2 * ‖Model.residual G.matrix (fun _ => 0) z g‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply Full.Nonlinear.large_height_stability G.matrix (fun _ => 0) z m g
    (Foundations.maxRowSum G.matrix) 1 ‖Model.residual G.matrix (fun _ => 0) z g‖
    (norm_nonneg _) zero_le_one le_rfl (norm_nonneg _) G.matrix_nonnegative
    (fun j => (le_abs_self _).trans (by
      simpa [Foundations.maxRowSum] using norm_le_pi_norm (fun j => ∑ k,G.matrix j k) j))
    hm heq hg
    (fun j => (norm_le_pi_norm (g-m) j).trans hclose)
    (fun j => (norm_le_pi_norm _ j).trans hres)
    (fun j => norm_le_pi_norm _ j) hheight i

end NonSymmetricDyson.Paper.Nonlinear
