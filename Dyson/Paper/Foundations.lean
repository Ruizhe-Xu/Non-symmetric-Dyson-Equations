import Dyson.Full.Foundations
import Dyson.Full.Norms

/-! Paper-facing M1. The support radius is exactly the manuscript's
unnormalized Euclidean potential norm, not the sharper sup-norm radius.
This compatibility backend uses continuation and Herglotz representation.
The faithful concrete infinite-tree Hilbert route is now independently
proved in `Paper.FoundationsTree`, with equal canonical measures. -/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory

namespace NonSymmetricDyson.Paper.Foundations
variable {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)

def potentialNorm : ℝ := ‖WithLp.toLp 2 a‖
def sigma : ℝ := potentialNorm a + 2 * Real.sqrt (Full.Foundations.maxRowSum S)

abbrev solution (hS : ∀ i j, 0 ≤ S i j) : ℂ → Fin n → ℂ :=
  GlobalWellPosedness.solution S a hS

theorem potential_component_le (i : Fin n) : |a i| ≤ potentialNorm a := by
  simpa [potentialNorm] using PiLp.norm_apply_le (WithLp.toLp 2 a) i

theorem sigma_nonnegative : 0 ≤ sigma S a := by
  unfold sigma potentialNorm
  positivity

/-- `thm:Existence and uniqueness`, with its exact radius and hypotheses. -/
theorem existence_and_uniqueness (hn : 0 < n)
    (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
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
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Full.Foundations.main_theorem_one external a hS (norm_nonneg _) (norm_nonneg _)
    (potential_component_le a) (fun i => (le_abs_self _).trans
      (norm_le_pi_norm (fun i => ∑ j, S i j) i))

/-- A definite choice of the unique M1 measures, used in the following paper
statements. This is a definition from proved existence, not an assumption. -/
def measure (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (hS : ∀ i j, 0 ≤ S i j) : Fin n → Measure ℝ :=
  (existence_and_uniqueness S a hn external hS).2.2.2.choose

theorem measure_spec (hn : 0 < n) (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (hS : ∀ i j, 0 ≤ S i j) (i : Fin n) :
    IsProbabilityMeasure (measure S a hn external hS i) ∧
    Full.Foundations.Represents (fun z => solution S a hS z i) (measure S a hn external hS i) ∧
    measure S a hn external hS i (Set.Icc (-(sigma S a)) (sigma S a))ᶜ = 0 ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Full.Foundations.Represents (fun z => solution S a hS z i) ν →
      ν = measure S a hn external hS i :=
  (existence_and_uniqueness S a hn external hS).2.2.2.choose_spec i

theorem solution_upper (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsUpperSolution (solution S a hS z) :=
  GlobalWellPosedness.solution_upper a hS hz

theorem solution_equation (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsDysonSolution S a z (solution S a hS z) :=
  GlobalWellPosedness.solution_equation a hS hz

end NonSymmetricDyson.Paper.Foundations
