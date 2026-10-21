import Dyson.PhaseDefect
import Dyson.IrreduciblePositivity

/-!
The full zero-edge-defect characterization, `lem.zero-set-of-edge-defect`.
Circle-valued entries encode the manuscript's unitary diagonal matrices.
Matrix irreducibility is converted to strong connectivity by a proved lemma.
-/

noncomputable section

namespace NonSymmetricDyson.MatrixResonance

open Manuscript.PositivityCorrection

variable {n : ℕ}

def delta (Q : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → Circle) : ℝ :=
  PhaseDefect.delta (fun i j => 0 < Q i j) v

/-- This is precisely the complex edge error used in the manuscript. -/
theorem edgeDefect_formula (Q : Matrix (Fin n) (Fin n) ℝ)
    (v gamma : Fin n → Circle) :
    PhaseDefect.edgeDefect (fun i j => 0 < Q i j) v gamma =
      ‖fun e : PhaseDefect.Edge (fun i j => 0 < Q i j) =>
        (v e.val.1 : ℂ) - star (gamma e.val.1 : ℂ) * (gamma e.val.2 : ℂ)‖ := by
  unfold PhaseDefect.edgeDefect
  congr 1
  funext e
  simp only [PhaseDefect.edgeError, Circle.coe_mul, Circle.coe_inv_eq_conj,
    Complex.star_def]

/-- Full matrix form of the paper's zero-defect/resonance lemma.
Positive dimension is stated explicitly through `[NeZero n]`. -/
theorem zero_defect_iff_cycle_resonance [NeZero n]
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Nonnegative Q) (hirr : Manuscript.PositivityCorrection.Irreducible Q)
    (v : Fin n → Circle) :
    delta Q v = 0 ↔ Resonance.CycleResonant (fun i j => 0 < Q i j) v := by
  exact PhaseDefect.delta_eq_zero_iff_cycleResonant _ v (0 : Fin n)
    (support_stronglyConnected_of_irreducible Q hQ hirr)

/-- Every phase infimum is attained, including before irreducibility is used. -/
theorem exists_minimizing_gauge (Q : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → Circle) :
    ∃ gamma : Fin n → Circle,
      delta Q v = PhaseDefect.edgeDefect (fun i j => 0 < Q i j) v gamma := by
  obtain ⟨gamma, hmin⟩ := PhaseDefect.exists_minimizer (fun i j => 0 < Q i j) v
  exact ⟨gamma, PhaseDefect.delta_eq_minimum _ v gamma hmin⟩

end NonSymmetricDyson.MatrixResonance
