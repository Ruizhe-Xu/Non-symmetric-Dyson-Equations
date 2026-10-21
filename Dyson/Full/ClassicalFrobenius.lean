import Dyson.Full.PerronExistence
import Mathlib.NumberTheory.FrobeniusNumber

/-! Exact interfaces for the two *explicitly cited standard facts* in the
manuscript's Auxiliary Results paragraph. They are retained external inputs,
as authorized, not claimed as internally proved Dyson results. In particular
the period is the actual gcd of positive return times, and simplicity on the
spectral circle is algebraic simplicity of the actual characteristic polynomial. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.ClassicalFrobenius
open Manuscript.PositivityCorrection

def returnPeriod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  Nat.setGcd {k : ℕ | 0 < k ∧ 0 < (A^k) i i}

/-- Cyclic normal form without an arbitrary ordering of the blocks. The
surjective class map gives the partition; its edge equation gives the cyclic
block form. The last two clauses give block diagonal powers and primitivity. -/
def CyclicDecomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∃ cls : Fin n → ZMod p,
    Function.Surjective cls ∧
    (∀ i, returnPeriod A i = p) ∧
    (∀ i j, 0 < A i j → cls j = cls i + 1) ∧
    (∀ c : ZMod p, ∃ i j, cls i = c ∧ cls j = c+1 ∧ 0 < A i j) ∧
    (∀ i j, cls i ≠ cls j → (A^p) i j = 0) ∧
    (∀ c : ZMod p, ∃ N : ℕ, 0 < N ∧ ∀ k ≥ N,
      ∀ i j, cls i = c → cls j = c → 0 < (A^(p*k)) i j)

def PerronSpectralConclusion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∃ l r : Fin n → ℝ,
    (∀ i, 0 < l i) ∧ (∀ i, 0 < r i) ∧
    (∀ i, ∑ j, A i j*r j = lam*r i) ∧
    (∀ j, ∑ i, l i*A i j = lam*l j) ∧
    (A.map Complex.ofRealHom).charpoly.IsRoot (lam : ℂ) ∧
    (∀ z : ℂ, (A.map Complex.ofRealHom).charpoly.IsRoot z → ‖z‖ ≤ lam) ∧
    (∀ z : ℂ, (A.map Complex.ofRealHom).charpoly.IsRoot z → ‖z‖ = lam →
      (A.map Complex.ofRealHom).charpoly.derivative.eval z ≠ 0)

/-- Both inputs are universal finite-matrix facts, independent of Dyson
equations. These are the two standard auxiliary lemmas cited in the source. -/
structure ExternalCitedFrobeniusTheory : Prop where
  cyclic : ∀ (n : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    Nonnegative A → Manuscript.PositivityCorrection.Irreducible A → CyclicDecomposition A
  spectral : ∀ (n : ℕ), 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    Nonnegative A → Manuscript.PositivityCorrection.Irreducible A → PerronSpectralConclusion A

theorem cited_cyclic_decomposition (external : ExternalCitedFrobeniusTheory)
    (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Manuscript.PositivityCorrection.Irreducible A) : CyclicDecomposition A :=
  external.cyclic n hn A hA hirr

theorem cited_perron_spectral_theorem (external : ExternalCitedFrobeniusTheory)
    (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Manuscript.PositivityCorrection.Irreducible A) : PerronSpectralConclusion A :=
  external.spectral n hn A hA hirr

end NonSymmetricDyson.Full.ClassicalFrobenius
