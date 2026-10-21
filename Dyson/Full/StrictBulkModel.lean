import Dyson.Full.StrictBulk
import Dyson.Full.BoundarySupport
import Dyson.Full.BoundaryExterior
import Dyson.Full.BulkGraph

/-! The literal separated strict-bulk energy set of the manuscript, with
compactness, regularity and all-coordinate positivity derived from the
actual Dyson family and its M1 representing measures. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.StrictBulkModel
open Resonance
variable {V : Type*} [Fintype V]

def energySet (m : ℂ → V → ℂ) (i : V) (ε : ℝ) : Set ℝ :=
  Boundary.regularSupport m i ∩
    StrictBulk.separated (frontier (Boundary.regularSupport m i) ∪ Boundary.singularUnion m) ε

/-- Positivity of a single boundary component propagates through actual
support walks. No Perron vector or comparison bound is assumed. -/
theorem boundary_upper_of_positive
    (S : Matrix V V ℝ) (a : V → ℝ) (τ : ℝ) (b : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (hy : ∀ i, 0 ≤ (b i).im)
    (heq : BasicEstimates.IsDysonSolution S a (τ : ℂ) b)
    (i : V) (hi : 0 < (b i).im) : BasicEstimates.IsUpperSolution b := by
  have hstep (j k : V) (hjk : S j k ≠ 0) (hj : (b j).im = 0) : (b k).im = 0 := by
    have hid := BasicEstimates.imaginary_part_identity heq j
    have hsum : ∑ t, S j t * (b t).im = 0 := by
      simpa [hj] using hid.symm
    have hterm : S j k * (b k).im ≤ 0 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun t _ => mul_nonneg (hS j t) (hy t)) (Finset.mem_univ k)
    have hpos : 0 < S j k := lt_of_le_of_ne (hS j k) (Ne.symm hjk)
    have hk : (b k).im ≤ 0 := (mul_le_mul_left hpos).mp (by simpa using hterm)
    exact le_antisymm hk (hy k)
  intro j
  by_contra hj
  have hj0 : (b j).im = 0 := le_antisymm (le_of_not_gt hj) (hy j)
  obtain ⟨p⟩ := hc j i
  exact hi.ne' (BulkGraph.along_walk hstep p hj0)

/-- The strict-bulk set is compact, avoids the actual singular set and has
strictly positive canonical boundary values in every component. -/
theorem energySet_data
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : V → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (i : V) (ε : ℝ) (hε : 0 < ε) :
    IsCompact (energySet m i ε) ∧
    (∀ E ∈ energySet m i ε, E ∉ Boundary.singularUnion m) ∧
    (∀ E ∈ energySet m i ε,
      BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) := by
  have hopen := Boundary.family_regularSupport_open algebraic puiseux S a hS m hupper heq i
  have hsubset := Boundary.regularSupport_subset_support_interval m μ σ hμ hsupport hrep i
  have hcompact : IsCompact (closure (Boundary.regularSupport m i)) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsubset isClosed_Icc)
  refine ⟨StrictBulk.strict_bulk_compact _ _ hopen hcompact ε hε,
    fun E hE => hE.1.1, ?_⟩
  intro E hE
  have hb := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq E hE.1.1
  exact boundary_upper_of_positive S a E _ hS hc hb.2.1 hb.2.2 i hE.1.2

/-- The energy set is independent of the chosen coordinate, just as the
regular support is; this version uses support connectivity directly. -/
theorem energySet_eq
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (i j : V) (ε : ℝ) : energySet m i ε = energySet m j ε := by
  have hsupp : Boundary.regularSupport m i = Boundary.regularSupport m j := by
    have hprop (i j : V) : Boundary.regularSupport m i ⊆ Boundary.regularSupport m j := by
      intro E hE
      have hb := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq E hE.1
      exact ⟨hE.1,boundary_upper_of_positive S a E _ hS hc hb.2.1 hb.2.2 i hE.2 j⟩
    exact Subset.antisymm (hprop i j) (hprop j i)
  simp only [energySet,hsupp]

end NonSymmetricDyson.Full.StrictBulkModel

namespace NonSymmetricDyson.Full.StrictBulkModel
open Set MeasureTheory Resonance
variable {V : Type*} [Fintype V] [Nonempty V]

/-- The preceding data for the canonical solution, including the construction
of its probability measures and support radius from M1. -/
theorem canonical_energySet_data
    (ext : Foundations.ExternalStieltjesTheory V)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => S i j ≠ 0))
    (i : V) (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution S a hS
    IsCompact (energySet m i ε) ∧
    (∀ E ∈ energySet m i ε, E ∉ Boundary.singularUnion m) ∧
    (∀ E ∈ energySet m i ε,
      BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) := by
  obtain ⟨_,_,_,μ,hμ⟩ := Foundations.main_theorem_one_max_norm ext a hS
  exact energySet_data algebraic puiseux S a hS hc _
    (fun z hz => GlobalWellPosedness.solution_upper a hS hz)
    (fun z hz => GlobalWellPosedness.solution_equation a hS hz)
    μ (fun j => (hμ j).1) (fun j => (hμ j).2.1)
    (Foundations.supportRadius S a) (fun j => (hμ j).2.2.1) i ε hε

end NonSymmetricDyson.Full.StrictBulkModel
