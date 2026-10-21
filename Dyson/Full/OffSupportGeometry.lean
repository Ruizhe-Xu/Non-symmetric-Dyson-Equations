import Dyson.Full.MainDecomposition
import Dyson.Full.StrictBulk

/-! The geometric off-support region used in the paper really supplies the
almost-everywhere measure gap used in the analytic inverse estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
namespace NonSymmetricDyson.Full.Boundary
open ExternalAlgebraic BoundaryMeasure Foundations

theorem density_atoms_concentrated
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (A : Finset ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (ha : ∀ x ∈ A, x ∈ B)
    (hf : ∀ x ∉ B, f x = 0)
    (heq : μ = volume.withDensity f + ∑ x ∈ A, μ {x} • Measure.dirac x) :
    ∀ᵐ x ∂μ, x ∈ B := by
  change μ Bᶜ = 0
  rw [heq, Measure.add_apply, withDensity_apply _ hB.compl,
    Measure.finset_sum_apply]
  have hz : ∫⁻ x in Bᶜ, f x = 0 := by
    calc
      _ = ∫⁻ _x in Bᶜ, (0 : ℝ≥0∞) :=
        setLIntegral_congr_fun hB.compl (fun x hx => hf x hx)
      _ = 0 := by simp
  rw [hz, zero_add]
  apply Finset.sum_eq_zero
  intro x hx
  simp [Measure.smul_apply, Measure.dirac_apply' _ hB.compl, ha x hx]

theorem family_ae_regular_closure_or_singular {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i)) (i j : Fin n) :
    ∀ᵐ t ∂μ j, t ∈ closure (regularSupport m i) ∪ singularUnion m := by
  obtain ⟨A,hA,hdecomp⟩ := family_measure_decomposition algebraic puiseux inversion S a hS m
    hupper heq μ hμ hrep j
  have hfin := family_singular_finite algebraic puiseux S a hS m hupper heq
  have hcommon := family_regularSupport_eq hn algebraic puiseux S a hS hirr m hupper heq j i
  apply density_atoms_concentrated (μ j)
    (boundaryDensity (fun z => boundaryVector m z j)) A _
    (isClosed_closure.union hfin.isClosed |>.measurableSet) ?_ ?_ hdecomp
  · intro t ht
    right
    apply Set.mem_iUnion.mpr
    exact ⟨j, by simpa only [← hA, Finset.mem_coe] using ht⟩
  · intro t ht
    have hs : t ∉ singularUnion m := fun hh => ht (Or.inr hh)
    have hi : t ∉ regularSupport m i := fun hh => ht (Or.inl (subset_closure hh))
    have hj : t ∉ regularSupport m j := by simpa only [hcommon] using hi
    have him : (boundaryVector m (t : ℂ) j).im ≤ 0 := by
      by_contra h
      exact hj ⟨hs, lt_of_not_ge h⟩
    exact ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg him Real.pi_pos.le)

/-- The pointwise separation definition also handles an empty singular set.
It supplies exactly the actual-measure gap required by M6 and M7 outside
the support. -/
theorem family_off_support_ae_gap {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (i : Fin n) (E ε : ℝ)
    (hsep : E ∈ StrictBulk.separated (closure (regularSupport m i) ∪ singularUnion m) ε) :
    ∀ j, ∀ᵐ t ∂μ j, ε ≤ |t-E| := by
  intro j
  filter_upwards [family_ae_regular_closure_or_singular hn algebraic puiseux inversion
    S a hS hirr m hupper heq μ hμ hrep i j] with t ht
  simpa only [abs_sub_comm] using hsep t ht

end NonSymmetricDyson.Full.Boundary
