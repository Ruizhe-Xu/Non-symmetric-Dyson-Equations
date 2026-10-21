import Mathlib
import Dyson.Existence
import Dyson.Uniqueness
import Dyson.SolutionClosedness
import Dyson.LocalSolvability
import Dyson.SolutionContinuity

/-!
# Global existence and uniqueness: continuation assembly

The nonempty seed is obtained from the proved Banach theorem. The upper
half-plane is connected. Local solvability and closedness of the existence
set are proved in their own modules and are assembled here.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.GlobalWellPosedness

open BasicEstimates Existence

variable {ι : Type*} [Fintype ι]

/-- Parameters in the open complex upper half-plane. -/
abbrev UpperParameter := {z : ℂ // 0 < z.im}

/-- Parameters at which an upper-half-plane solution exists. -/
def existenceSet (S : ι → ι → ℝ) (a : ι → ℝ) : Set UpperParameter :=
  {z | ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a z.val m}

theorem upperParameter_connected : ConnectedSpace UpperParameter := by
  apply Subtype.connectedSpace
  exact (convex_halfSpace_im_gt (0 : ℝ)).isConnected
    ⟨Complex.I, by simp⟩

/-- The existence set is nonempty for every nonnegative finite matrix.
The explicit parameter has imaginary part `1 + ∑ᵢⱼ Sᵢⱼ`. -/
theorem existenceSet_nonempty {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) : (existenceSet S a).Nonempty := by
  let M : ℝ := ∑ i, ∑ j, S i j
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => hS i j
  let z₀ : ℂ := ⟨0, M + 1⟩
  have hz₀ : 0 < z₀.im := by change 0 < M + 1; linarith
  have hrow : ∀ i, ∑ j, S i j ≤ z₀.im ^ 2 / 2 := by
    intro i
    have hi : ∑ j, S i j ≤ M :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => hS k j)
        (Finset.mem_univ i)
    change ∑ j, S i j ≤ (M + 1) ^ 2 / 2
    nlinarith [sq_nonneg M]
  exact ⟨⟨z₀, hz₀⟩, exists_upper_solution_large_im hS hz₀ hrow⟩

theorem existenceSet_isClosed {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) : IsClosed (existenceSet S a) :=
  SolutionClosedness.solution_set_isClosed hS

theorem existenceSet_isOpen {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) : IsOpen (existenceSet S a) :=
  LocalSolvability.isOpen_solvable_upper S a hS

/-- The elementary connectedness step in the continuation argument.
The open and closed assertions are intermediate hypotheses here; the final
global theorem below discharges them using the separate proved modules. -/
theorem existenceSet_eq_univ_of_open_closed {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hopen : IsOpen (existenceSet S a))
    (hclosed : IsClosed (existenceSet S a)) : existenceSet S a = Set.univ := by
  letI : ConnectedSpace UpperParameter := upperParameter_connected
  exact IsClopen.eq_univ ⟨hclosed, hopen⟩ (existenceSet_nonempty a hS)

/-- Every upper-half-plane parameter admits a genuine upper-half-plane Dyson
solution. No symmetry, irreducibility, or row-sum restriction is imposed. -/
theorem upper_half_plane_exists {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ}
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im) :
    ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a z m := by
  have hall : existenceSet S a = Set.univ :=
    existenceSet_eq_univ_of_open_closed a hS
      (existenceSet_isOpen a hS) (existenceSet_isClosed a hS)
  have hmem : (⟨z, hz⟩ : UpperParameter) ∈ existenceSet S a := by
    rw [hall]
    exact Set.mem_univ _
  exact hmem

/-- The existence-and-uniqueness assertion of the manuscript's
`thm:Existence and uniqueness`, with exactly its nonnegativity assumption.
The analytic and Stieltjes-representation assertions are separate statements. -/
theorem upper_half_plane_exists_unique {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ}
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im) :
    ∃! m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a z m := by
  obtain ⟨m, hm, hsol⟩ := upper_half_plane_exists (a := a) hS hz
  refine ⟨m, ⟨hm, hsol⟩, ?_⟩
  intro n hn
  exact Uniqueness.upper_half_plane_unique hS hz hn.1 hm hn.2 hsol

/-- The earlier concrete interface target is now proved, rather than merely
declared as a proposition. -/
theorem wellPosednessTarget {S : Matrix ι ι ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) : Model.WellPosednessTarget S a := by
  intro z hz
  exact upper_half_plane_exists_unique hS hz

/-- The canonical solution family, extended by zero outside the upper
half-plane solely to give it a total complex-domain function type. -/
def solution (S : ι → ι → ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (z : ℂ) : ι → ℂ :=
  if hz : 0 < z.im then (upper_half_plane_exists (a := a) hS hz).choose else 0

theorem solution_upper {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) :
    IsUpperSolution (solution S a hS z) := by
  simp only [solution, dif_pos hz]
  exact (upper_half_plane_exists (a := a) hS hz).choose_spec.1

theorem solution_equation {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) :
    IsDysonSolution S a z (solution S a hS z) := by
  simp only [solution, dif_pos hz]
  exact (upper_half_plane_exists (a := a) hS hz).choose_spec.2

theorem solution_eq_of_upper_solution {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) {m : ι → ℂ}
    (hm : IsUpperSolution m) (hsol : IsDysonSolution S a z m) :
    solution S a hS z = m :=
  Uniqueness.upper_half_plane_unique hS hz (solution_upper a hS hz) hm
    (solution_equation a hS hz) hsol

theorem solution_norm_le {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) (i : ι) :
    ‖solution S a hS z i‖ ≤ z.im⁻¹ :=
  rough_bound hS hz (solution_upper a hS hz) (solution_equation a hS hz) i

/-- Continuity of the canonical family on the upper-half-plane parameter
space, derived from the proved continuity theorem for actual solution families. -/
theorem solution_continuous {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) :
    Continuous (fun z : UpperParameter => solution S a hS z.val) :=
  SolutionContinuity.solution_family_continuous hS _
    (fun z => solution_upper a hS z.property)
    (fun z => solution_equation a hS z.property)

theorem solution_continuousOn {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) :
    ContinuousOn (solution S a hS) {z : ℂ | 0 < z.im} :=
  continuousOn_iff_continuous_restrict.mpr (solution_continuous a hS)

/-- The canonical Dyson solution is analytic at every upper-half-plane
parameter. Its local analytic branches come from the proved inverse-function
theorem construction and agree globally by uniqueness. -/
theorem solution_analyticOnNhd {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) :
    AnalyticOnNhd ℂ (solution S a hS) {z : ℂ | 0 < z.im} :=
  LocalSolvability.analyticOnNhd_of_solution_family S a (solution S a hS) hS
    (fun _ hz => solution_upper a hS hz)
    (fun _ hz => solution_equation a hS hz)

theorem solution_analyticAt {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (solution S a hS) z :=
  solution_analyticOnNhd a hS z hz

theorem solution_differentiableOn {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) :
    DifferentiableOn ℂ (solution S a hS) {z : ℂ | 0 < z.im} :=
  (solution_analyticOnNhd a hS).differentiableOn


end NonSymmetricDyson.GlobalWellPosedness
