import Dyson.Full.BoundaryPuiseux
import Dyson.Full.BoundaryMeasure
import Dyson.GlobalWellPosedness

/-!
# Applying the algebraic boundary construction to the actual Dyson solution

The external parameters here are generic algebraic and scalar Stieltjes
theorems. Boundary limits, continuous extensions, measure decompositions,
and equality of the regular positive-density sets are derived.
-/

noncomputable section
open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryMeasure

variable {ι : Type*} [Fintype ι]

def singularUnion (m : ℂ → ι → ℂ) : Set ℝ :=
  ⋃ i, singularSet (fun z => m z i)

def boundaryVector (m : ℂ → ι → ℂ) (z : ℂ) (i : ι) : ℂ :=
  boundaryExtension (fun w => m w i) z

def commonRegularDomain (m : ℂ → ι → ℂ) : Set ℂ :=
  upper ∪ Complex.ofReal '' (singularUnion m)ᶜ

theorem family_coordinate_analytic (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i : ι) :
    AnalyticOnNhd ℂ (fun z => m z i) upper := by
  intro z hz
  exact analyticAt_pi_iff.mp
    (LocalSolvability.analyticOnNhd_of_solution_family S a m hS hupper heq z hz) i

theorem family_singular_finite
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) :
    (singularUnion m).Finite := by
  apply Set.finite_iUnion
  intro i
  exact (algebraic_boundary_alternative puiseux (fun z => m z i)
    (family_coordinate_analytic S a hS m hupper heq i)
    (solution_algebraic algebraic S a hS m hupper heq i)
    (fun z hz => hupper z hz i)).1

theorem family_boundary_limits
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ singularUnion m) :
    IsBoundaryValue m τ (boundaryVector m (τ : ℂ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hi : τ ∉ singularSet (fun z => m z i) :=
    fun h => hτ (Set.mem_iUnion.mpr ⟨i, h⟩)
  exact (algebraic_continuous_extension puiseux (fun z => m z i)
    (family_coordinate_analytic S a hS m hupper heq i)
    (solution_algebraic algebraic S a hS m hupper heq i)
    (fun z hz => hupper z hz i)).2.2 τ hi

theorem family_boundary_equation
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ singularUnion m) :
    (∀ i, boundaryVector m (τ : ℂ) i ≠ 0) ∧
    (∀ i, 0 ≤ (boundaryVector m (τ : ℂ) i).im) ∧
    BasicEstimates.IsDysonSolution S a (τ : ℂ) (boundaryVector m (τ : ℂ)) :=
  boundary_equation S a m τ _
    (family_boundary_limits algebraic puiseux S a hS m hupper heq τ hτ) hupper heq

theorem family_boundary_continuous
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) :
    ContinuousOn (boundaryVector m) (commonRegularDomain m) := by
  apply continuousOn_pi.mpr
  intro i
  apply (algebraic_continuous_extension puiseux (fun z => m z i)
    (family_coordinate_analytic S a hS m hupper heq i)
    (solution_algebraic algebraic S a hS m hupper heq i)
    (fun z hz => hupper z hz i)).1.mono
  rintro z (hz | ⟨τ, hτ, rfl⟩)
  · exact Or.inl hz
  · exact Or.inr ⟨τ, (fun hi => hτ (Set.mem_iUnion.mpr ⟨i, hi⟩)), rfl⟩

/-- The actual density-plus-finite-atom decomposition, with the singular
set obtained from the algebraic equations rather than supplied as input. -/
theorem family_measure_decomposition
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i)) (i : ι) :
    ∃ A : Finset ℝ, (A : Set ℝ) = singularSet (fun z => m z i) ∧
      μ i = densityMeasure (fun z => boundaryVector m z i) +
        ∑ τ ∈ A, μ i {τ} • Measure.dirac τ := by
  classical
  have ha := family_coordinate_analytic S a hS m hupper heq i
  have halg := solution_algebraic algebraic S a hS m hupper heq i
  have hp : ∀ z ∈ upper, 0 < (m z i).im := fun z hz => hupper z hz i
  have hfin := (algebraic_boundary_alternative puiseux (fun z => m z i) ha halg hp).1
  have hcont := algebraic_continuous_extension puiseux (fun z => m z i) ha halg hp
  refine ⟨hfin.toFinset, by simp, ?_⟩
  apply finite_exceptional_decomposition inversion (μ i) (fun z => m z i)
    (fun z => boundaryVector m z i) hfin.toFinset (hμ i) (hrep i)
  · simpa [boundaryDomain, regularDomain, boundaryVector] using hcont.1
  · exact hcont.2.1

def regularSupport (m : ℂ → ι → ℂ) (i : ι) : Set ℝ :=
  {τ | τ ∉ singularUnion m ∧ 0 < (boundaryVector m (τ : ℂ) i).im}

/-- The manuscript's regular support is independent of the coordinate,
proved from the boundary Dyson equation and irreducibility. -/
theorem family_regularSupport_eq {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i j : Fin n) :
    regularSupport m i = regularSupport m j := by
  ext τ
  constructor <;> rintro ⟨hτ, hpos⟩
  · have hb := family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
    exact ⟨hτ, (boundary_positive_iff hn S hS hirr a τ _ hb.1 hb.2.1 hb.2.2 i j).mp hpos⟩
  · have hb := family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
    exact ⟨hτ, (boundary_positive_iff hn S hS hirr a τ _ hb.1 hb.2.1 hb.2.2 j i).mp hpos⟩

def closedStrip (I : Set ℝ) : Set ℂ := {z | z.re ∈ I ∧ 0 ≤ z.im}

/-- Closed-strip continuity follows from the interior bound even for an
unbounded set I. No compactness of I is used at this step. -/
theorem family_closedStrip_continuous
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (I : Set ℝ) (M : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M) :
    ContinuousOn (boundaryVector m) (closedStrip I) := by
  apply (family_boundary_continuous algebraic puiseux S a hS m hupper heq).mono
  intro z hz
  by_cases hi : 0 < z.im
  · exact Or.inl hi
  · have hz0 : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2
    refine Or.inr ⟨z.re, ?_, ?_⟩
    · intro hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      apply not_singular_of_bounded (f := fun w => m w i) (M := M) ?_ hi
      intro η hη
      exact hbound (vertical z.re η) (by simpa [vertical] using hz.1) (by simpa using hη) i
    · exact Complex.ext (by simp) (by simpa using hz0.symm)

end NonSymmetricDyson.Full.Boundary
