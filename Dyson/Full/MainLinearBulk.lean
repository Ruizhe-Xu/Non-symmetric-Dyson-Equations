import Dyson.Full.BulkCompact
import Dyson.Full.EuclideanInverse
import Dyson.Full.Poisson

noncomputable section
open scoped BigOperators Topology

namespace NonSymmetricDyson.Full.MainLinearBulk
variable {V : Type*} [Fintype V] [Nonempty V]

def closedStrip (J : Set ℝ) : Set ℂ := {z | z.re ∈ J ∧ 0 ≤ z.im}
def boundedStrip (J : Set ℝ) (H : ℝ) : Set ℂ :=
  {z | z.re ∈ J ∧ 0 ≤ z.im ∧ z.im ≤ H}

theorem boundedStrip_compact (J : Set ℝ) (hJ : IsCompact J) (H : ℝ) :
    IsCompact (boundedStrip J H) := by
  have heq : boundedStrip J H =
      (fun p : ℝ × ℝ => Poisson.point p.1 p.2) '' (J ×ˢ Set.Icc 0 H) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re,z.im), ⟨hz.1,hz.2⟩, ?_⟩
      apply Complex.ext <;> simp [Poisson.point]
    · rintro ⟨⟨E,η⟩, ⟨hE,hη⟩, rfl⟩
      simpa [boundedStrip, Poisson.point] using And.intro hE hη
  rw [heq]
  apply (hJ.prod isCompact_Icc).image
  have he : (fun p : ℝ × ℝ => Poisson.point p.1 p.2) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ)*Complex.I) := by
    funext p
    apply Complex.ext <;> simp [Poisson.point]
  rw [he]
  fun_prop

/-- The compact boundary argument is extended to every positive height,
and both sides are expressed in the actual Euclidean inverse norm. -/
theorem full_strip_inverse_bounds
    (J : Set ℝ) (hJ : IsCompact J) (S : Matrix V V ℝ) (a : V → ℝ)
    (m : ℂ → V → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution S a z (m z))
    (hboundary : ∀ E ∈ J, Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C := by
  let R : ℝ := ‖fun i => ∑ j, S i j‖
  have hR : 0 ≤ R := norm_nonneg _
  have hrow (i : V) : ∑ j, S i j ≤ R :=
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H : ℝ := 1 + 2*R
  have hH : 0 < H := by dsimp [H]; positivity
  let K := boundedStrip J H
  have hK := boundedStrip_compact J hJ H
  have hsub : K ⊆ closedStrip J := fun _ hz => ⟨hz.1,hz.2.1⟩
  have hbij : ∀ z ∈ K, Function.Bijective (InteriorStability.stabilityOperator S (m z)) := by
    intro z hz
    by_cases hi : 0 < z.im
    · exact InteriorStability.stability_bijective hS hi (hupper z (hsub hz)) (hsol z (hsub hz))
    · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2.1
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hi0)
      simpa only [← he] using hboundary z.re hz.1
  obtain ⟨A, hA, hlow⟩ := BulkCompact.uniform_dyson_bound K hK S m (hcont.mono hsub) hbij
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  let M : ℝ := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmod : ∀ z : ℂ, z.re ∈ J → 0 < z.im → ∀ i, ‖m z i‖ ≤ M := by
    intro z hE hz i
    by_cases hh : z.im ≤ H
    · exact (norm_le_pi_norm _ i).trans ((hM₀ z ⟨hE,hz.le,hh⟩).trans (le_max_right _ _))
    · have hHi : 1 ≤ z.im := by dsimp [H] at hh; linarith
      have hb := BasicEstimates.rough_bound hS hz (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) i
      exact hb.trans ((inv_le_one₀ hz).mpr hHi |>.trans (le_max_left _ _))
  have hbound : ∀ z : ℂ, z.re ∈ J → 0 < z.im → ∀ x,
      ‖x‖ ≤ max A 2 * ‖InteriorStability.stabilityOperator S (m z) x‖ := by
    intro z hE hz x
    by_cases hh : z.im ≤ H
    · exact (hlow z ⟨hE,hz.le,hh⟩ x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · have hs : ∀ i, 2*∑ j, S i j ≤ z.im^2 := by
        intro i
        have hh' : H < z.im := lt_of_not_ge hh
        have hHsq : 2*R ≤ H^2 := by dsimp [H]; nlinarith
        nlinarith [hrow i]
      exact (Linear.high_height_lower_norm_bound S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) hs x).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  let d : ℝ := Real.sqrt (Fintype.card V)
  have hd : 0 < d := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  refine ⟨(1/(1+M^2*R))/d, d*max A 2, by positivity, by positivity, ?_⟩
  intro z hE hz
  constructor
  · have hl := Linear.inverse_norm_lower_bound S a z (m z) hS hz
      (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) M R hM.le hR (hmod z hE hz) hrow
    have he := EuclideanInverse.conjugate_norm_lower
      (InteriorStability.stabilityContinuousEquiv hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)).symm.toContinuousLinearMap
    apply (div_le_iff₀ hd).mpr
    exact (hl.trans he).trans_eq (mul_comm _ _)
  · exact EuclideanInverse.stability_inverse_upper S a z (m z) hS hz
      (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) (max A 2) (by positivity) (hbound z hE hz)

/-- M6 stable-bulk clause for symmetric support, over the whole vertical strip. -/
theorem main_theorem_six_symmetric_bulk
    (J : Set ℝ) (hJ : IsCompact J) (S : Matrix V V ℝ) (a : V → ℝ)
    (m : ℂ → V → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution S a z (m z))
    (hc : Resonance.StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hexception : ∀ E ∈ J, ¬ ((∀ i, a i = E) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C := by
  apply full_strip_inverse_bounds J hJ S a m hS hcont hupper hsol
  intro E hE
  exact BulkBoundary.symmetric_boundary_bijective S a E (m (E : ℂ)) hS hc hsymm
    (hupper _ ⟨by simpa using hE, by simp⟩)
    (hsol _ ⟨by simpa using hE, by simp⟩) (hexception E hE)

namespace NB
open Nonbacktracking

/-- The same full-height conclusion for the actual non-backtracking matrix
and terminal vertex potential; the exception concerns the base graph. -/
theorem main_theorem_six_bulk
    (G : BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (J : Set ℝ) (hJ : IsCompact J) (a : V → ℝ) (m : ℂ → G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G)
    (hc : Resonance.StronglyConnected G.Adj)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J,
      BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (hexception : ∀ E ∈ J, ¬ ((∀ i, a i = E) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c ≤ ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
        G.matrix_nonnegative hz (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse G.matrix (G.terminalShift a) z (m z)
        G.matrix_nonnegative hz (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C := by
  letI : Nonempty G.Edge := ⟨root⟩
  apply full_strip_inverse_bounds J hJ G.matrix (G.terminalShift a) m
    G.matrix_nonnegative hcont hupper hsol
  intro E hE
  exact BulkBoundary.NB.boundary_bijective G a E (m (E : ℂ)) hd root hc
    (hupper _ ⟨by simpa using hE, by simp⟩)
    (hsol _ ⟨by simpa using hE, by simp⟩) (hexception E hE)

end NB
end NonSymmetricDyson.Full.MainLinearBulk
