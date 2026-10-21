import Dyson.Full.ClassicalFrobenius
import Dyson.Full.ReducibleBlocks
import Dyson.Full.WeightedNonbacktracking
import Dyson.Full.FoundationsSchur

/-! Exact cited preliminary facts and the purely finite algebra in the
introduction. External assumptions here are universal matrix/graph theorems,
not conclusions about Dyson solutions. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.FoundationsPreliminaries
universe u
open Full.ClassicalFrobenius Manuscript.PositivityCorrection

/-- `lem:cyclic-decomp`. The class map is the partition, and the support
identity is its permutation-independent cyclic block form. Only primitivity,
as stated in the paper, is retained from the classical eventual-positivity input. -/
theorem cyclic_decomposition (external : ExternalCitedFrobeniusTheory)
    (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Manuscript.PositivityCorrection.Irreducible A) :
    ∃ p : ℕ, 0 < p ∧ ∃ cls : Fin n → ZMod p,
      Function.Surjective cls ∧
      (∀ i, returnPeriod A i = p) ∧
      (∀ i j, 0 < A i j → cls j = cls i + 1) ∧
      (∀ c : ZMod p, ∃ i j, cls i = c ∧ cls j = c+1 ∧ 0 < A i j) ∧
      (∀ i j, cls i ≠ cls j → (A^p) i j = 0) ∧
      (∀ c : ZMod p, ∃ N : ℕ, 0 < N ∧
        ∀ i j, cls i = c → cls j = c → 0 < (A^(p*N)) i j) := by
  obtain ⟨p, hp, cls, hs, hperiod, he, hnonzero, hblock, hprimitive⟩ :=
    external.cyclic n hn A hA hirr
  refine ⟨p, hp, cls, hs, hperiod, he, hnonzero, hblock, ?_⟩
  intro c
  obtain ⟨N, hN, hh⟩ := hprimitive c
  exact ⟨N, hN, hh N le_rfl⟩

/-- `lem.PF`: the positive eigenvalue dominates every eigenvalue in modulus,
and every eigenvalue on that actual spectral circle is an algebraically
simple root of the characteristic polynomial. -/
theorem perron_frobenius (external : ExternalCitedFrobeniusTheory)
    (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Nonnegative A) (hirr : Manuscript.PositivityCorrection.Irreducible A) :
    PerronSpectralConclusion A :=
  external.spectral n hn A hA hirr

/-- The reducible-matrix paragraph: an actual ordered SCC decomposition
makes the equation block recursive. A loopless singleton is a zero block;
the forcing coming from later blocks is complex, with Im at least Im z. -/
theorem recursive_blocks {V : Type u} [Fintype V]
    (external : Full.ReducibleBlocks.ExternalFiniteSCCOrdering.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ d : Full.ReducibleBlocks.OrderedComponents (fun i j => 0 < S i j),
      (∀ i j : Σ c, Full.ReducibleBlocks.Block d c, j.1 < i.1 →
        Full.ReducibleBlocks.blockedMatrix S d i j = 0) ∧
      (∀ c : Fin d.count,
        (∀ i j : Full.ReducibleBlocks.Block d c, ∃ k : ℕ, 0 < k ∧
          0 < (Full.ReducibleBlocks.diagonalBlock S d c ^ k) i j) ∨
        (Nonempty (Full.ReducibleBlocks.Block d c) ∧
          Subsingleton (Full.ReducibleBlocks.Block d c) ∧
          Full.ReducibleBlocks.diagonalBlock S d c = 0)) ∧
      (∀ (a : V → ℝ) (z : ℂ) (m : V → ℂ),
        BasicEstimates.IsDysonSolution S a z m ↔
          ∀ i, -(m i)⁻¹ = Full.ReducibleBlocks.forcing S a z d m i +
            Full.ReducibleBlocks.diagonalInteraction S d m i) :=
  Full.ReducibleBlocks.exists_recursive_block_decomposition external S hS

/-- The weighted universal-cover application's finite algebraic step:
forward-neighbor recursion is precisely a vector Dyson equation with the
Jacobi square weights and terminal-vertex potential. This does not assert
construction of the infinite-tree Hilbert operator. -/
theorem weighted_forward_recursion {V : Type*} [Fintype V]
    (G : Nonbacktracking.BaseGraph V) (b : V → V → ℝ) (a : V → ℝ)
    (z : ℂ) (m : G.Edge → ℂ) :
    Full.WeightedNonbacktracking.IsForwardRecursion G b a z m ↔
      BasicEstimates.IsDysonSolution (Full.WeightedNonbacktracking.matrix G b)
        (G.terminalShift a) z m :=
  Full.WeightedNonbacktracking.forward_recursion_iff_dyson G b a z m

end NonSymmetricDyson.Paper.FoundationsPreliminaries
