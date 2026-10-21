import Dyson.Paper.TreeSolution

/-! M1 with the concrete type-word tree proof from the corrected blueprint.
The spectral input is entirely general; the actual tree operators, root
Schur recursion, positivity, Dyson existence and support radius are derived.
This file supplies the faithful M1 endpoint, independently of Herglotz
representation or the alternative finite-dimensional continuation proof. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace NonSymmetricDyson.Paper.FoundationsTree
open Paper.Foundations
variable {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)

theorem row_bound (i : Fin n) : (∑ j, S i j) ≤ Full.Foundations.maxRowSum S :=
  (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)

/-- The full original M1 statement, obtained by constructing root spectral
measures on actual ℓ² type-word trees. Its support radius is exactly the
manuscript's unnormalized Euclidean `|a|₂+2√‖S‖∞`. -/
theorem tree_existence_and_uniqueness (hn : 0 < n)
    (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (hS : ∀ i j, 0 ≤ S i j) :
    Model.WellPosednessTarget S a ∧
    AnalyticOnNhd ℂ (solution S a hS) {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ∀ i, ‖solution S a hS z i‖ ≤ z.im⁻¹) ∧
    ∃ μ : Fin n → Measure ℝ, ∀ i,
      IsProbabilityMeasure (μ i) ∧
      Full.Foundations.Represents (fun z => solution S a hS z i) (μ i) ∧
      μ i (Set.Icc (-(sigma S a)) (sigma S a))ᶜ = 0 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Full.Foundations.Represents (fun z => solution S a hS z i) ν → ν = μ i := by
  let A := potentialNorm a
  let R := Full.Foundations.maxRowSum S
  have hA : 0 ≤ A := norm_nonneg _
  have hR : 0 ≤ R := norm_nonneg _
  have ha := potential_component_le a
  have hr := row_bound S
  refine ⟨TreeSolution.wellPosedness S a hS A R hA hR ha hr spectral,
    TreeSolution.canonical_analytic S a hS A R hA hR ha hr spectral,
    fun z hz i => TreeSolution.canonical_norm_le S a hS A R hA hR ha hr spectral hz i,?_⟩
  choose μ hμ hs hrep using TreeSolution.canonical_measure S a hS A R hA hR ha hr spectral
  refine ⟨μ,fun i => ⟨hμ i,hrep i,hs i,?_⟩⟩
  intro ν hν hνrep
  exact TreeSpectral.measure_unique unique (fun z => solution S a hS z i) ν (μ i)
    hν (hμ i) hνrep (hrep i)

/-- The definite canonical measures selected from the tree-backed M1. -/
def measure (hn : 0 < n)
    (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (hS : ∀ i j, 0 ≤ S i j) : Fin n → Measure ℝ :=
  (tree_existence_and_uniqueness S a hn spectral unique hS).2.2.2.choose

theorem measure_spec (hn : 0 < n)
    (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (hS : ∀ i j, 0 ≤ S i j) (i : Fin n) :
    IsProbabilityMeasure (measure S a hn spectral unique hS i) ∧
    Full.Foundations.Represents (fun z => solution S a hS z i)
      (measure S a hn spectral unique hS i) ∧
    measure S a hn spectral unique hS i (Set.Icc (-(sigma S a)) (sigma S a))ᶜ = 0 ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Full.Foundations.Represents (fun z => solution S a hS z i) ν →
      ν = measure S a hn spectral unique hS i :=
  (tree_existence_and_uniqueness S a hn spectral unique hS).2.2.2.choose_spec i

/-- The tree measures and the earlier canonical measure implementation
are literally equal, so later statements refer to the same measures. -/
theorem measure_eq_previous (hn : 0 < n)
    (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (hS : ∀ i j, 0 ≤ S i j) :
    measure S a hn spectral unique hS = Foundations.measure S a hn external hS := by
  funext i
  exact (Foundations.measure_spec S a hn external hS i).2.2.2 _
    (measure_spec S a hn spectral unique hS i).1
    (measure_spec S a hn spectral unique hS i).2.1

end NonSymmetricDyson.Paper.FoundationsTree
