import Dyson.Full.MainLinearExterior
import Dyson.Full.OffSupportGeometry

/-! The geometric outside region in M6, for the canonical solution itself.
The probability measures, support radius, and almost-everywhere gap are
constructed from the earlier theorems rather than assumed here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace NonSymmetricDyson.Full.OffSupport

theorem main_theorem_six_exterior_model {n : ℕ} (hn : 0 < n)
    (ext : Foundations.ExternalStieltjesTheory (Fin n))
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    let m := GlobalWellPosedness.solution S a hS
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ E η : ℝ, ∀ hη : 0 < η,
      E ∈ StrictBulk.separated
        (closure (Boundary.regularSupport m i) ∪ Boundary.singularUnion m) ε →
      let z := Poisson.point E η
      let hz : 0 < z.im := hη
      c ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (GlobalWellPosedness.solution_upper a hS hz)
        (GlobalWellPosedness.solution_equation a hS hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (GlobalWellPosedness.solution_upper a hS hz)
        (GlobalWellPosedness.solution_equation a hS hz)‖ ≤ C := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let m := GlobalWellPosedness.solution S a hS
  obtain ⟨_, _, _, μ, hμ⟩ := Foundations.main_theorem_one_max_norm ext a hS
  have hp : ∀ j, IsProbabilityMeasure (μ j) := fun j => (hμ j).1
  have hrep : ∀ j, Foundations.Represents (fun z => m z j) (μ j) :=
    fun j => (hμ j).2.1
  have hs : ∀ j, ∀ᵐ t ∂μ j, |t| ≤ Foundations.supportRadius S a := by
    intro j
    have hh : ∀ᵐ t ∂μ j, t ∈ Icc (-(Foundations.supportRadius S a))
        (Foundations.supportRadius S a) := by
      change μ j (Icc (-(Foundations.supportRadius S a)) (Foundations.supportRadius S a))ᶜ = 0
      exact (hμ j).2.2.1
    exact hh.mono fun t ht => abs_le.mpr ht
  have hu : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z) :=
    fun z hz => GlobalWellPosedness.solution_upper a hS hz
  have he : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z) :=
    fun z hz => GlobalWellPosedness.solution_equation a hS hz
  have hm : ∀ z : ℂ, 0 < z.im → (fun j => Poisson.stieltjes (μ j) z) = m z := by
    intro z hz
    funext j
    exact (hrep j z hz).symm
  have hus : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun j => Poisson.stieltjes (μ j) z) := by
    intro z hz
    rw [hm z hz]
    exact hu z hz
  have hes : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun j => Poisson.stieltjes (μ j) z) := by
    intro z hz
    rw [hm z hz]
    exact he z hz
  obtain ⟨c,C,hc,hC,hbound⟩ := main_theorem_six_exterior S a μ hp hS
    ‖a‖ (Foundations.maxRowSum S) (Foundations.supportRadius S a) ε
    (norm_nonneg _) (norm_nonneg _) (by unfold Foundations.supportRadius; positivity) hε
    (fun j => by simpa using norm_le_pi_norm a j)
    (fun j => (le_abs_self _).trans (by
      simpa [Foundations.maxRowSum] using norm_le_pi_norm (fun j => ∑ k, S j k) j))
    hs hus hes
  refine ⟨c,C,hc,hC,?_⟩
  intro E η hη hsep
  have hgap := Boundary.family_off_support_ae_gap hn algebraic puiseux inversion
    S a hS hirr m hu he μ hp hrep i E ε hsep
  have hb := hbound E η hη hgap
  simpa only [hm (Poisson.point E η) hη] using hb

end NonSymmetricDyson.Full.OffSupport
