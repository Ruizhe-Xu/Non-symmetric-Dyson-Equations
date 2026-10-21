import Mathlib
import Dyson.Full.Foundations

/-!
# Stieltjes inversion and the finite exceptional set

Only scalar Stieltjes inversion and the scalar atom formula are external.
The decomposition into an actual density measure and finitely many atoms,
and the implications of the atom formula, are proved in Lean below.
-/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter MeasureTheory

namespace NonSymmetricDyson.Full.BoundaryMeasure

open Foundations

def boundaryDomain (U : Set ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ Complex.ofReal '' U

def boundaryDensity (F : ℂ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((F (x : ℂ)).im / Real.pi)

def densityMeasure (F : ℂ → ℂ) : Measure ℝ :=
  volume.withDensity (boundaryDensity F)

instance densityMeasure_noAtoms (F : ℂ → ℂ) : NoAtoms (densityMeasure F) := by
  unfold densityMeasure
  infer_instance

/-- Two standard, scalar Stieltjes theorems, with no Dyson content. -/
structure ExternalStieltjesInversion : Prop where
  inversion : ∀ (μ : Measure ℝ) (f F : ℂ → ℂ) (U : Set ℝ),
    IsProbabilityMeasure μ → Represents f μ → IsOpen U →
    ContinuousOn F (boundaryDomain U) →
    (∀ z : ℂ, 0 < z.im → F z = f z) →
    μ.restrict U = (densityMeasure F).restrict U
  atom_formula : ∀ (μ : Measure ℝ) (f : ℂ → ℂ) (τ : ℝ),
    IsProbabilityMeasure μ → Represents f μ →
    Tendsto (fun η : ℝ => η * (f (vertical τ η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 ((μ {τ}).toReal))

/-- A measure restricted to a finite set is exactly the sum of its point masses. -/
theorem restrict_finset_eq_sum (μ : Measure ℝ) (A : Finset ℝ) :
    μ.restrict (A : Set ℝ) = ∑ τ ∈ A, μ {τ} • Measure.dirac τ := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert τ A hτ ih =>
    have hd : Disjoint ({τ} : Set ℝ) (A : Set ℝ) := by
      simp [hτ]
    rw [Finset.coe_insert, Set.insert_eq, Measure.restrict_union hd
      A.finite_toSet.measurableSet, Measure.restrict_singleton, ih,
      Finset.sum_insert hτ]

/-- Exact measure decomposition from agreement off a finite set. -/
theorem decomposition_of_restrict_compl {μ ν : Measure ℝ}
    (A : Finset ℝ) [NoAtoms ν]
    (h : μ.restrict (A : Set ℝ)ᶜ = ν.restrict (A : Set ℝ)ᶜ) :
    μ = ν + ∑ τ ∈ A, μ {τ} • Measure.dirac τ := by
  calc
    μ = μ.restrict (A : Set ℝ)ᶜ + μ.restrict (A : Set ℝ) :=
      (Measure.restrict_compl_add_restrict A.finite_toSet.measurableSet).symm
    _ = ν.restrict (A : Set ℝ)ᶜ + ∑ τ ∈ A, μ {τ} • Measure.dirac τ := by
      rw [h, restrict_finset_eq_sum]
    _ = _ := by rw [A.finite_toSet.countable.measure_restrict_compl ν]

/-- The full density-plus-finitely-many-atoms conclusion from a continuous
boundary extension outside the finite exceptional set. -/
theorem finite_exceptional_decomposition (ext : ExternalStieltjesInversion)
    (μ : Measure ℝ) (f F : ℂ → ℂ) (A : Finset ℝ)
    (hμ : IsProbabilityMeasure μ) (hrep : Represents f μ)
    (hcont : ContinuousOn F (boundaryDomain (A : Set ℝ)ᶜ))
    (hagrees : ∀ z : ℂ, 0 < z.im → F z = f z) :
    μ = densityMeasure F + ∑ τ ∈ A, μ {τ} • Measure.dirac τ := by
  apply decomposition_of_restrict_compl A
  exact ext.inversion μ f F (A : Set ℝ)ᶜ hμ hrep
    A.finite_toSet.isClosed.isOpen_compl hcont hagrees

/-- A positive atom necessarily forces the imaginary Stieltjes transform
to diverge to positive infinity along the vertical line. -/
theorem imaginary_tendsto_atTop_of_atom (ext : ExternalStieltjesInversion)
    (μ : Measure ℝ) (f : ℂ → ℂ) (τ : ℝ)
    (hμ : IsProbabilityMeasure μ) (hrep : Represents f μ)
    (hτ : μ {τ} ≠ 0) :
    Tendsto (fun η : ℝ => (f (vertical τ η)).im) (𝓝[>] (0 : ℝ)) atTop := by
  letI := hμ
  have hmass : 0 < (μ {τ}).toReal := ENNReal.toReal_pos hτ (measure_ne_top μ _)
  have hprod := (ext.atom_formula μ f τ hμ hrep).pos_mul_atTop hmass
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : η ≠ 0 := ne_of_gt hη
  simp [mul_assoc, mul_comm, hη']

/-- A finite vertical imaginary boundary value excludes an atom. -/
theorem atom_eq_zero_of_finite_limit (ext : ExternalStieltjesInversion)
    (μ : Measure ℝ) (f : ℂ → ℂ) (τ L : ℝ)
    (hμ : IsProbabilityMeasure μ) (hrep : Represents f μ)
    (hlim : Tendsto (fun η : ℝ => (f (vertical τ η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) : μ {τ} = 0 := by
  letI := hμ
  have hzero : Tendsto (fun η : ℝ => η) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun η : ℝ => η * (f (vertical τ η)).im)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hzero.mul hlim
  have heq : (μ {τ}).toReal = 0 :=
    tendsto_nhds_unique (ext.atom_formula μ f τ hμ hrep) hprod
  exact ((ENNReal.toReal_eq_zero_iff _).mp heq).resolve_right (measure_ne_top μ _)

/-- If the finitely many exceptional points also have finite boundary limits,
the atomic term disappears entirely. -/
theorem density_only_of_finite_limits (ext : ExternalStieltjesInversion)
    (μ : Measure ℝ) (f F : ℂ → ℂ) (A : Finset ℝ)
    (hμ : IsProbabilityMeasure μ) (hrep : Represents f μ)
    (hcont : ContinuousOn F (boundaryDomain (A : Set ℝ)ᶜ))
    (hagrees : ∀ z : ℂ, 0 < z.im → F z = f z)
    (hlimits : ∀ τ ∈ A, ∃ L : ℝ,
      Tendsto (fun η : ℝ => (f (vertical τ η)).im) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    μ = densityMeasure F := by
  have hatoms : ∀ τ ∈ A, μ {τ} = 0 := by
    intro τ hτ
    obtain ⟨L, hL⟩ := hlimits τ hτ
    exact atom_eq_zero_of_finite_limit ext μ f τ L hμ hrep hL
  have hsum : (∑ τ ∈ A, μ {τ} • Measure.dirac τ) = 0 := by
    apply Finset.sum_eq_zero
    intro τ hτ
    rw [hatoms τ hτ, zero_smul]
  rw [finite_exceptional_decomposition ext μ f F A hμ hrep hcont hagrees,
    hsum, add_zero]

theorem densityMeasure_absolutelyContinuous (F : ℂ → ℂ) :
    densityMeasure F ≪ (volume : Measure ℝ) :=
  withDensity_absolutelyContinuous volume (boundaryDensity F)

end NonSymmetricDyson.Full.BoundaryMeasure
