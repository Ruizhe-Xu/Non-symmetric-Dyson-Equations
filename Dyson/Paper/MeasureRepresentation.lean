import Dyson.Full.Foundations

noncomputable section
open MeasureTheory
namespace NonSymmetricDyson.Paper.MeasureRepresentation
open Full.Foundations
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- M1's actual measures represent every upper Dyson solution, by uniqueness;
no separate representation hypothesis is needed by the later model endpoints. -/
theorem upper_solution_probability_representation
    (external : ExternalStieltjesTheory ι)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z)) :
    ∃ μ : ι → Measure ℝ, ∀ i, IsProbabilityMeasure (μ i) ∧
      Represents (fun z => m z i) (μ i) := by
  obtain ⟨μ,hμ⟩ := canonical_probability_representation external a hS
  refine ⟨μ,fun i => ⟨(hμ i).1,?_⟩⟩
  intro z hz
  have hm := Uniqueness.upper_half_plane_unique hS hz (hupper z hz)
    (GlobalWellPosedness.solution_upper a hS hz) (heq z hz)
    (GlobalWellPosedness.solution_equation a hS hz)
  change m z i = _
  rw [hm]
  exact (hμ i).2 z hz

end NonSymmetricDyson.Paper.MeasureRepresentation
