import Dyson.Paper.WeightedTreeSolution
import Dyson.Full.WeightedNonbacktracking

/-! Signed Jacobi realization of the introductory forward NB recursion.
The Hilbert space consists of actual admissible NB words rooted at an edge;
each creation edge carries the original signed real Jacobi coefficient.
No positivity or nonvanishing of those coefficients is required. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.WeightedNBTree
universe u
variable {V : Type u} [Fintype V] (G : Nonbacktracking.BaseGraph V)
variable (b : V → V → ℝ) (a : V → ℝ)

def coupling (_e f : G.Edge) : ℝ := b (G.tail f) (G.head f)

def potentialBound : ℝ := ‖G.terminalShift a‖

def rowEnergy (e : G.Edge) : ℝ :=
  ∑ f : {f : G.Edge // 0<G.matrix e f}, coupling G b e f.val ^ 2

def energyBound : ℝ := ‖rowEnergy G b‖

theorem potentialBound_nonnegative : 0≤potentialBound G a := norm_nonneg _
theorem energyBound_nonnegative : 0≤energyBound G b := norm_nonneg _

theorem potential_le (e : G.Edge) : |G.terminalShift a e|≤potentialBound G a := by
  simpa only [potentialBound,Real.norm_eq_abs] using norm_le_pi_norm (G.terminalShift a) e

theorem rowEnergy_le (e : G.Edge) : rowEnergy G b e≤energyBound G b :=
  (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (rowEnergy G b) e)

/-- The finite Dyson matrix is exactly the paper's weighted NB matrix,
including zero and negative original Jacobi weights. -/
theorem coefficient_eq :
    WeightedTreeSolution.coefficient G.matrix (coupling G b)=
      Full.WeightedNonbacktracking.matrix G b := by
  funext e f
  by_cases h : G.CanFollow e f
  · simp [WeightedTreeSolution.coefficient,Nonbacktracking.BaseGraph.matrix,
      Full.WeightedNonbacktracking.matrix,coupling,h]
  · simp [WeightedTreeSolution.coefficient,Nonbacktracking.BaseGraph.matrix,
      Full.WeightedNonbacktracking.matrix,coupling,h]

/-- The actual signed bounded self-adjoint Jacobi operator on the forward
word tree. Its diagonal is the potential at the terminal vertex. -/
abbrev jacobi (e : G.Edge) :=
  WeightedTreeModel.jacobi G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) e

theorem jacobi_selfAdjoint (e : G.Edge) : IsSelfAdjoint (jacobi G b a e) :=
  WeightedTreeModel.jacobi_selfAdjoint G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) e

theorem jacobi_norm_le (e : G.Edge) :
    ‖jacobi G b a e‖≤potentialBound G a+2*Real.sqrt (energyBound G b) :=
  WeightedTreeModel.norm_jacobi G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) e

variable (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{u})

def transform (z : ℂ) : G.Edge → ℂ :=
  WeightedTreeSolution.transform G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) spectral z

/-- This is the root matrix element of the inverse of the actual signed
Jacobi operator, rather than a function merely assumed to satisfy recursion. -/
theorem root_green (z : ℂ) (e : G.Edge) :
    transform G b a spectral z e = inner ℂ (WeightedTreeModel.delta G.matrix e)
      ((WeightedTreeSolution.data G.matrix (coupling G b) (G.terminalShift a)
        (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
        (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) spectral e).green z
          (WeightedTreeModel.delta G.matrix e)) :=
  WeightedTreeSolution.transform_inner G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) spectral z e

theorem transform_upper {z : ℂ} (hz : 0<z.im) :
    BasicEstimates.IsUpperSolution (transform G b a spectral z) :=
  WeightedTreeSolution.transform_upper G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) spectral hz

theorem transform_equation {z : ℂ} (hz : 0<z.im) :
    BasicEstimates.IsDysonSolution (Full.WeightedNonbacktracking.matrix G b)
      (G.terminalShift a) z (transform G b a spectral z) := by
  rw [← coefficient_eq G b]
  exact WeightedTreeSolution.transform_equation G.matrix (coupling G b) (G.terminalShift a)
    (potentialBound G a) (energyBound G b) (potentialBound_nonnegative G a)
    (energyBound_nonnegative G b) (potential_le G a) (rowEnergy_le G b) spectral hz

/-- Literal `eq.QVE-NB`, derived by deleting the actual root of the signed
tree operator and identifying its child sum with vertex neighbors. -/
theorem forward_recursion {z : ℂ} (hz : 0<z.im) :
    Full.WeightedNonbacktracking.IsForwardRecursion G b a z (transform G b a spectral z) :=
  (Full.WeightedNonbacktracking.forward_recursion_iff_dyson G b a z _).mpr
    (transform_equation G b a spectral hz)

/-- The realized Green family is the canonical finite Dyson solution. -/
theorem canonical_eq {z : ℂ} (hz : 0<z.im) :
    GlobalWellPosedness.solution (Full.WeightedNonbacktracking.matrix G b)
      (G.terminalShift a) (Full.WeightedNonbacktracking.matrix_nonnegative G b) z =
      transform G b a spectral z :=
  GlobalWellPosedness.solution_eq_of_upper_solution (G.terminalShift a)
    (Full.WeightedNonbacktracking.matrix_nonnegative G b) hz
    (transform_upper G b a spectral hz) (transform_equation G b a spectral hz)

end NonSymmetricDyson.Paper.WeightedNBTree
