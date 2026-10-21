import Dyson.Full.MainDecomposition

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

/-- Actual positive-density real boundary values approaching a regular
frontier point. This connects the support topology to Perron analysis at
an edge or cusp; the sequence satisfies the Dyson equation at every term. -/
theorem regular_frontier_sequence {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (regularSupport m i))
    (hτ : τ ∉ singularUnion m) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 τ) ∧
      (∀ k, E k ∉ singularUnion m) ∧
      (∀ k j, 0 < (boundaryVector m (E k : ℂ) j).im) ∧
      (∀ k, BasicEstimates.IsDysonSolution S a (E k : ℂ)
        (boundaryVector m (E k : ℂ))) ∧
      Tendsto (fun k => boundaryVector m (E k : ℂ)) atTop
        (𝓝 (boundaryVector m (τ : ℂ))) := by
  obtain ⟨E, hE, ht⟩ := mem_closure_iff_seq_limit.mp hfront.1
  have hnot : ∀ k, E k ∉ singularUnion m := fun k => (hE k).1
  refine ⟨E, ht, hnot, ?_, ?_, ?_⟩
  · intro k j
    have hco := family_regularSupport_eq hn algebraic puiseux S a hS hirr m hupper heq i j
    have hm : E k ∈ regularSupport m j := hco ▸ hE k
    exact hm.2
  · intro k
    exact (family_boundary_equation algebraic puiseux S a hS m hupper heq (E k) (hnot k)).2.2
  · have hcz : Tendsto (fun k => (E k : ℂ)) atTop (𝓝 (τ : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    have hwithin : Tendsto (fun k => (E k : ℂ)) atTop
        (𝓝[commonRegularDomain m] (τ : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hcz, Filter.Eventually.of_forall ?_⟩
      intro k
      exact Or.inr ⟨E k, hnot k, rfl⟩
    exact ((family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      (τ : ℂ) (Or.inr ⟨τ, hτ, rfl⟩)).tendsto.comp hwithin

end NonSymmetricDyson.Full.Boundary
