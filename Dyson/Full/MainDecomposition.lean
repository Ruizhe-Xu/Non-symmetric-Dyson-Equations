import Dyson.Full.BoundarySupport
import Dyson.Full.BoundaryExterior
import Dyson.Full.MainRegularity

/-! The finite singular set, exact measure decomposition, and common finite
interval support, for the actual Dyson solution family. The density chosen
here is the finite regular boundary representative; changing its values on
the finite singular set does not change the density measure. -/

noncomputable section
open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryMeasure BoundaryTopology Foundations

theorem family_regularSupport_finite_intervals {ι : Type*} [Fintype ι]
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (topology : ExternalFiniteBoundaryIntervals)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0) (i : ι) :
    ∃ (k : ℕ) (l r : Fin k → ℝ), (∀ j, l j < r j) ∧
      Pairwise (fun j t => Disjoint (Ioo (l j) (r j)) (Ioo (l t) (r t))) ∧
      regularSupport m i = ⋃ j, Ioo (l j) (r j) ∧
      closure (regularSupport m i) = ⋃ j, Icc (l j) (r j) := by
  apply finite_open_and_closed_intervals topology (regularSupport m i)
    (family_regularSupport_open algebraic puiseux S a hS m hupper heq i)
    (regularSupport_subset_support_interval m μ σ hμ hsupport hrep i)
  intro τ _
  exact family_regularSupport_one_sided algebraic puiseux S a hS m hupper heq i τ

/-- Every atom is one of the finitely many singular points. Zero atom
weights need not be removed from the finite sum in the measure identity. -/
theorem atom_mem_singular (inversion : ExternalStieltjesInversion)
    (μ : Measure ℝ) (f : ℂ → ℂ) (hμ : IsProbabilityMeasure μ)
    (hrep : Represents f μ) (τ : ℝ) (hτ : μ {τ} ≠ 0) : τ ∈ singularSet f := by
  apply norm_diverges_of_imaginary
  exact imaginary_tendsto_atTop_of_atom inversion μ f τ hμ hrep hτ

theorem family_density_continuous_regular {ι : Type*} [Fintype ι]
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i : ι) :
    ContinuousOn (realDensity m i) (singularUnion m)ᶜ := by
  have hc := continuousOn_pi.mp
    (family_boundary_continuous algebraic puiseux S a hS m hupper heq) i
  have hr := hc.comp Complex.continuous_ofReal.continuousOn
    (show MapsTo Complex.ofReal (singularUnion m)ᶜ (commonRegularDomain m) from
      fun x hx => Or.inr ⟨x, hx, rfl⟩)
  exact (Complex.continuous_im.comp_continuousOn hr).div_const Real.pi

/-- M2, with an explicit density representative and exact equality of
measures. Every singular set and boundary value in this statement is
constructed from m itself; none is an input hypothesis. -/
theorem main_theorem_two {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion) (topology : ExternalFiniteBoundaryIntervals)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0) :
    (∀ i,
      (singularSet (fun z => m z i)).Finite ∧
      singularSet (fun z => m z i) ⊆ Icc (-σ) σ ∧
      (∀ τ, τ ∈ singularSet (fun z => m z i) ↔
        Tendsto (fun η => (m (vertical τ η) i).im) (𝓝[>] (0 : ℝ)) atTop) ∧
      ContinuousOn (fun z => boundaryVector m z i) (regularDomain (fun z => m z i)) ∧
      (∀ τ ∉ singularSet (fun z => m z i),
        Tendsto (fun η => m (vertical τ η) i) (𝓝[>] (0 : ℝ))
          (𝓝 (boundaryVector m (τ : ℂ) i))) ∧
      (∃ A : Finset ℝ, (A : Set ℝ) = singularSet (fun z => m z i) ∧
        μ i = volume.withDensity (fun x => ENNReal.ofReal (realDensity m i x)) +
          ∑ τ ∈ A, μ i {τ} • Measure.dirac τ) ∧
      (∀ τ : ℝ, Tendsto (fun η => η * (m (vertical τ η) i).im)
        (𝓝[>] (0 : ℝ)) (𝓝 ((μ i {τ}).toReal)))) ∧
    (singularUnion m).Finite ∧
    (∀ i j, regularSupport m i = regularSupport m j) ∧
    (∀ i, ContinuousOn (realDensity m i) (regularSupport m i)) ∧
    ∃ (k : ℕ) (l r : Fin k → ℝ), (∀ j, l j < r j) ∧
      Pairwise (fun j t => Disjoint (Ioo (l j) (r j)) (Ioo (l t) (r t))) ∧
      ∀ i, regularSupport m i = ⋃ j, Ioo (l j) (r j) := by
  have hco := family_regularSupport_eq hn algebraic puiseux S a hS hirr m hupper heq
  refine ⟨?_, family_singular_finite algebraic puiseux S a hS m hupper heq, hco, ?_, ?_⟩
  · intro i
    letI := hμ i
    have ha := family_coordinate_analytic S a hS m hupper heq i
    have halg := solution_algebraic algebraic S a hS m hupper heq i
    have hPick : ∀ z ∈ upper, 0 < (m z i).im := fun z hz => hupper z hz i
    have hb := algebraic_boundary_alternative puiseux (fun z => m z i) ha halg hPick
    have hc := algebraic_continuous_extension puiseux (fun z => m z i) ha halg hPick
    refine ⟨hb.1, singularSet_subset_support_interval (μ i) (fun z => m z i) (hsupport i) (hrep i),
      hb.2.1, hc.1, hc.2.2, ?_, ?_⟩
    · exact family_measure_decomposition algebraic puiseux inversion S a hS m hupper heq μ hμ hrep i
    · intro τ
      exact inversion.atom_formula (μ i) (fun z => m z i) τ (hμ i) (hrep i)
  · intro i
    exact (family_density_continuous_regular algebraic puiseux S a hS m hupper heq i).mono
      (fun x hx => hx.1)
  · let i₀ : Fin n := ⟨0, hn⟩
    obtain ⟨k, l, r, hlr, hdis, hU, _⟩ := family_regularSupport_finite_intervals algebraic puiseux
      topology S a hS m hupper heq μ hμ hrep σ hsupport i₀
    exact ⟨k, l, r, hlr, hdis, fun i => (hco i i₀).trans hU⟩

end NonSymmetricDyson.Full.Boundary
