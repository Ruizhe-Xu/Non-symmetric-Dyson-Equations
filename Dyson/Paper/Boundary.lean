import Dyson.Paper.Foundations
import Dyson.Full.MainDecomposition
import Dyson.Full.PoleRemovedDensity
import Dyson.Paper.BoundaryAtoms

/-! M2 with the actual atom-subtracted, possibly infinite density. Every
object below is derived from the M1 canonical solution and its unique measure. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Paper.Boundary
open Full ExternalAlgebraic Full.Boundary Full.BoundaryMeasure
open Paper.Foundations
variable {n : ℕ}

/-- `lem:puiseux`: actual canonical coordinates have convergent fractional
power expansions. `PuiseuxChart` stores an analytic convergent Taylor factor,
an integer leading exponent, and the coherent positive-denominator root. -/
theorem puiseux_expansion
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S) (i : Fin n) (τ : ℝ) :
    Nonempty (PuiseuxChart (fun z => solution S a hS z i) τ) := by
  have ha := family_coordinate_analytic S a hS (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz) i
  have halg := solution_algebraic algebraic S a hS (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz) i
  have hnz : solution S a hS Complex.I i ≠ 0 := by
    exact BasicEstimates.component_ne_zero (solution_upper S a hS (by simp)) i
  exact (puiseux _ ha halg ⟨Complex.I, by simp [upper], hnz⟩).2 τ

/-- `thm.decompose of measure`: finite singularities and finite boundary values. -/
theorem singular_sets_and_boundary_values
    (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    let m := solution S a hS
    (∀ i, (singularSet (fun z => m z i)).Finite ∧
      (∀ τ, τ ∈ singularSet (fun z => m z i) ↔
        Tendsto (fun η => (m (Full.Foundations.vertical τ η) i).im)
          (𝓝[>] (0 : ℝ)) atTop) ∧
      ∀ τ ∉ singularSet (fun z => m z i),
        Tendsto (fun η => m (Full.Foundations.vertical τ η) i) (𝓝[>] (0 : ℝ))
          (𝓝 (boundaryVector m (τ : ℂ) i))) ∧ (singularUnion m).Finite := by
  dsimp only
  refine ⟨?_, family_singular_finite algebraic puiseux S a hS _
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz)⟩
  intro i
  have ha := family_coordinate_analytic S a hS (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz) i
  have halg := solution_algebraic algebraic S a hS (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz) i
  have hp : ∀ z ∈ upper, 0 < (solution S a hS z i).im :=
    fun z hz => solution_upper S a hS hz i
  have hb := algebraic_boundary_alternative puiseux _ ha halg hp
  exact ⟨hb.1, hb.2.1, (algebraic_continuous_extension puiseux _ ha halg hp).2.2⟩

/-- The density is the extended limit after subtracting the actual atomic
poles, exactly as in `def.vj-Delta`; finite zero-weight terms are allowed. -/
private theorem component_measure_decomposition_with_zero_weights
    (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (rational : RationalAlgebraicity) (inversion : ExternalStieltjesInversion)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (i : Fin n) :
    let m := solution S a hS
    let μ := measure S a hn external hS
    ∃ A : Finset ℝ, (A : Set ℝ) ⊆ singularSet (fun z => m z i) ∧
      let h := atomRemoved (μ i) (fun z => m z i) A
      (∀ τ ∈ A, Tendsto (fun η => η * (m (Full.Foundations.vertical τ η) i).im)
        (𝓝[>] (0 : ℝ)) (𝓝 ((μ i {τ}).toReal))) ∧
      (∀ x : ℝ, Tendsto (fun η => ENNReal.ofReal ((h (Full.Foundations.vertical x η)).im / Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 (extendedDensity h x))) ∧
      μ i = volume.withDensity (extendedDensity h) +
        ∑ τ ∈ A, μ i {τ} • Measure.dirac τ ∧
      ContinuousOn (extendedDensity h) (regularSupport m i) ∧
      {x : ℝ | x ∉ singularUnion m ∧ 0 < extendedDensity h x} = regularSupport m i := by
  dsimp only
  let m := solution S a hS
  let μ := measure S a hn external hS
  have hprob := fun j => (measure_spec S a hn external hS j).1
  have hrep := fun j => (measure_spec S a hn external hS j).2.1
  obtain ⟨A, hA, hlim, hreg, hcont, hdec, hzero, hexp⟩ :=
    pole_removed_density_decomposition algebraic puiseux rational inversion S a hS m
      (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz)
      μ hprob hrep i
  refine ⟨A, by rw [hA], ?_⟩
  refine ⟨fun τ _ => BoundaryAtoms.represented_atom_formula (μ i) (fun z => m z i) τ (hprob i) (hrep i),
    hlim, hdec, ?_, ?_⟩
  · apply hcont.mono
    intro x hx
    intro hxA
    apply hx.1
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change x ∈ singularSet (fun z => m z i)
    rw [← hA]
    exact hxA
  · ext x
    change (x ∉ singularUnion m ∧ 0 < extendedDensity (atomRemoved (μ i) (fun z => m z i) A) x) ↔ x ∈ regularSupport m i
    by_cases hx : x ∈ singularUnion m
    · simp [regularSupport, hx]
    · have hxA : x ∉ A := by
        intro h
        apply hx
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        rw [← hA]
        exact h
      rw [show extendedDensity (atomRemoved (μ i) (fun z => m z i) A) x =
        ENNReal.ofReal (realDensity m i x) from hreg x hxA]
      simp [regularSupport, hx, ENNReal.ofReal_pos, realDensity, Real.pi_pos]

/-- `eq.measure-decomposition` and `def.vj-Delta`, listing only strictly
positive atomic masses. The extended density is defined by the literal
atom-subtracted transform in the paper. -/
theorem component_measure_decomposition
    (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (rational : RationalAlgebraicity) (inversion : ExternalStieltjesInversion)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (i : Fin n) :
    let m := solution S a hS
    let μ := measure S a hn external hS
    ∃ A : Finset ℝ, (A : Set ℝ) ⊆ singularSet (fun z => m z i) ∧
      (∀ τ ∈ A, 0 < (μ i {τ}).toReal) ∧
      let h := atomRemoved (μ i) (fun z => m z i) A
      (∀ τ ∈ A, Tendsto (fun η => η * (m (Full.Foundations.vertical τ η) i).im)
        (𝓝[>] (0 : ℝ)) (𝓝 ((μ i {τ}).toReal))) ∧
      (∀ x : ℝ, Tendsto (fun η => ENNReal.ofReal ((h (Full.Foundations.vertical x η)).im / Real.pi))
        (𝓝[>] (0 : ℝ)) (𝓝 (extendedDensity h x))) ∧
      μ i = volume.withDensity (extendedDensity h) +
        ∑ τ ∈ A, μ i {τ} • Measure.dirac τ ∧
      ContinuousOn (extendedDensity h) (regularSupport m i) ∧
      {x : ℝ | x ∉ singularUnion m ∧ 0 < extendedDensity h x} = regularSupport m i := by
  dsimp only
  let m := solution S a hS
  let μ := measure S a hn external hS
  letI : IsProbabilityMeasure (μ i) := (measure_spec S a hn external hS i).1
  obtain ⟨A,hA,hatom,hlim,hdec,hcont,hpos⟩ :=
    component_measure_decomposition_with_zero_weights hn external algebraic puiseux rational
      inversion S a hS hirr i
  let B := BoundaryAtoms.positiveAtoms (μ i) A
  have hsub : B ⊆ A := BoundaryAtoms.positiveAtoms_subset (μ i) A
  have heq : atomRemoved (μ i) (fun z => m z i) B =
      atomRemoved (μ i) (fun z => m z i) A := BoundaryAtoms.atomRemoved_positiveAtoms _ _ _
  refine ⟨B, fun τ hτ => hA (hsub hτ), ?_, ?_⟩
  · intro τ hτ
    exact ENNReal.toReal_pos (BoundaryAtoms.positiveAtoms_positive (μ i) A hτ).ne'
      (measure_ne_top _ _)
  · refine ⟨fun τ hτ => hatom τ (hsub hτ), ?_, ?_, ?_, ?_⟩
    · simpa only [B, μ, m, BoundaryAtoms.atomRemoved_positiveAtoms] using hlim
    · simpa only [B, μ, m, BoundaryAtoms.atomRemoved_positiveAtoms, BoundaryAtoms.atomic_measure_positiveAtoms] using hdec
    · simpa only [B, μ, m, BoundaryAtoms.atomRemoved_positiveAtoms] using hcont
    · simpa only [B, μ, m, BoundaryAtoms.atomRemoved_positiveAtoms] using hpos

/-- The common support and its finite open-interval description. -/
theorem common_regular_support
    (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (topology : Full.BoundaryTopology.ExternalFiniteBoundaryIntervals)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    let m := solution S a hS
    (∀ i j, regularSupport m i = regularSupport m j) ∧
      ∃ (k : ℕ) (l r : Fin k → ℝ), (∀ j, l j < r j) ∧
        Pairwise (fun j t => Disjoint (Ioo (l j) (r j)) (Ioo (l t) (r t))) ∧
        ∀ i, regularSupport m i = ⋃ j, Ioo (l j) (r j) := by
  dsimp only
  have hco := family_regularSupport_eq hn algebraic puiseux S a hS hirr (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz)
  refine ⟨hco, ?_⟩
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨k,l,r,hlr,hdis,hset,_⟩ := family_regularSupport_finite_intervals algebraic puiseux
    topology S a hS (solution S a hS) (fun z hz => solution_upper S a hS hz)
    (fun z hz => solution_equation S a hS hz) (measure S a hn external hS)
    (fun i => (measure_spec S a hn external hS i).1)
    (fun i => (measure_spec S a hn external hS i).2.1) (sigma S a)
    (fun i => (measure_spec S a hn external hS i).2.2.1) i₀
  exact ⟨k,l,r,hlr,hdis,fun i => (hco i i₀).trans hset⟩

end NonSymmetricDyson.Paper.Boundary
