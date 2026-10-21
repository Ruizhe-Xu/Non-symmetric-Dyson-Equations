import Dyson.Full.MainLinearOrigin
import Dyson.GlobalWellPosedness

/-! Constant potential shifts are actual changes of spectral variable.
The stability inverse itself is unchanged; its weight becomes |z-a|^{-1}.
These identities justify every zero-potential normalization in the paper. -/

noncomputable section
open scoped Topology
namespace NonSymmetricDyson.Full.SpectralShift
variable {V : Type*} [Fintype V]

theorem dyson_shift (S : Matrix V V ℝ) (a : V → ℝ) (c : ℝ) (z : ℂ) (m : V → ℂ) :
    BasicEstimates.IsDysonSolution S (fun i => a i + c) z m ↔
      BasicEstimates.IsDysonSolution S a (z - (c : ℂ)) m := by
  unfold BasicEstimates.IsDysonSolution
  simp only [Complex.ofReal_add]
  congr! 2
  ring

theorem constant_dyson_shift (S : Matrix V V ℝ) (c : ℝ) (z : ℂ) (m : V → ℂ) :
    BasicEstimates.IsDysonSolution S (fun _ => c) z m ↔
      BasicEstimates.IsDysonSolution S (fun _ => 0) (z - (c : ℂ)) m := by
  simpa using dyson_shift S (fun _ => 0) c z m

theorem canonical_shift (S : Matrix V V ℝ) (a : V → ℝ) (c : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (z : ℂ) (hz : 0 < z.im) :
    GlobalWellPosedness.solution S (fun i => a i + c) hS z =
      GlobalWellPosedness.solution S a hS (z - (c : ℂ)) := by
  have hz' : 0 < (z - (c : ℂ)).im := by simpa using hz
  exact GlobalWellPosedness.solution_eq_of_upper_solution _ hS hz
    (GlobalWellPosedness.solution_upper a hS hz')
    ((dyson_shift S a c z _).mpr (GlobalWellPosedness.solution_equation a hS hz'))

theorem inverse_independent_of_presentation
    (S : Matrix V V ℝ) (a b : V → ℝ) (z w : ℂ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im) (hw : 0 < w.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hzsol : BasicEstimates.IsDysonSolution S a z m)
    (hwsol : BasicEstimates.IsDysonSolution S b w m) :
    EuclideanInverse.stabilityInverse S a z m hS hz hm hzsol =
      EuclideanInverse.stabilityInverse S b w m hS hw hm hwsol := by
  have he : InteriorStability.stabilityContinuousEquiv hS hz hm hzsol =
      InteriorStability.stabilityContinuousEquiv hS hw hm hwsol := by
    ext x i
    rfl
  unfold EuclideanInverse.stabilityInverse
  rw [he]

theorem inverse_shift
    (S : Matrix V V ℝ) (a : V → ℝ) (c : ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S (fun i => a i + c) z m) :
    EuclideanInverse.stabilityInverse S (fun i => a i + c) z m hS hz hm hsol =
      EuclideanInverse.stabilityInverse S a (z - (c : ℂ)) m hS (by simpa using hz) hm
        ((dyson_shift S a c z m).mp hsol) :=
  inverse_independent_of_presentation _ _ _ _ _ _ _ _ _ _ _ _

def shiftedInterval (J : Set ℝ) (c : ℝ) : Set ℝ :=
  (fun x => x - c) '' J

theorem shiftedInterval_compact (J : Set ℝ) (hJ : IsCompact J) (c : ℝ) :
    IsCompact (shiftedInterval J c) := hJ.image (continuous_id.sub continuous_const)

theorem shiftedInterval_mem (J : Set ℝ) (c x : ℝ) :
    x - c ∈ shiftedInterval J c ↔ x ∈ J := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hxy : y = x := by linarith
    simpa only [hxy] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

end NonSymmetricDyson.Full.SpectralShift
