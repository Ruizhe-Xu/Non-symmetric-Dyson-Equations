import Mathlib
import Dyson.Resonance

/-!
The analytic compactness step in `lem.zero-set-of-edge-defect`.
The supremum norm on the finite edge set is exactly the maximum edge defect
in the manuscript (and is zero if the edge set is empty).
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.PhaseDefect

variable {ι : Type*} [Fintype ι] (E : ι → ι → Prop) [DecidableRel E]

abbrev Edge := {p : ι × ι // E p.1 p.2}

def edgeError (v gamma : ι → Circle) : Edge E → ℂ :=
  fun e => (v e.val.1 : ℂ) - (((gamma e.val.1)⁻¹ * gamma e.val.2 : Circle) : ℂ)

def edgeDefect (v gamma : ι → Circle) : ℝ := ‖edgeError E v gamma‖

/-- The paper's infimum over vertex phases. -/
def delta (v : ι → Circle) : ℝ := sInf (Set.range (edgeDefect E v))

theorem edgeDefect_nonnegative (v gamma : ι → Circle) : 0 ≤ edgeDefect E v gamma :=
  norm_nonneg _

theorem edgeDefect_eq_zero_iff (v gamma : ι → Circle) :
    edgeDefect E v gamma = 0 ↔
      ∀ a b, E a b → v a = (gamma a)⁻¹ * gamma b := by
  rw [edgeDefect, norm_eq_zero]
  constructor
  · intro h a b hab
    apply Circle.coe_injective
    have he := congrFun h (⟨(a,b),hab⟩ : Edge E)
    change (v a : ℂ) - (((gamma a)⁻¹ * gamma b : Circle) : ℂ) = 0 at he
    exact sub_eq_zero.mp he
  · intro h
    funext e
    change (v e.val.1 : ℂ) - (((gamma e.val.1)⁻¹ * gamma e.val.2 : Circle) : ℂ) = 0
    rw [h _ _ e.property]
    exact sub_self _

theorem continuous_edgeDefect (v : ι → Circle) : Continuous (edgeDefect E v) := by
  unfold edgeDefect edgeError
  apply Continuous.norm
  apply continuous_pi
  intro e
  fun_prop

theorem exists_minimizer (v : ι → Circle) :
    ∃ gamma : ι → Circle, ∀ gamma', edgeDefect E v gamma ≤ edgeDefect E v gamma' := by
  obtain ⟨gamma, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (ι → Circle)).Nonempty)
    (continuous_edgeDefect E v).continuousOn
  exact ⟨gamma, fun gamma' => hmin (Set.mem_univ gamma')⟩

theorem delta_eq_minimum (v : ι → Circle) (gamma : ι → Circle)
    (hmin : ∀ gamma', edgeDefect E v gamma ≤ edgeDefect E v gamma') :
    delta E v = edgeDefect E v gamma := by
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro y ⟨g, rfl⟩; exact edgeDefect_nonnegative E v g⟩
      (Set.mem_range_self gamma)
  · exact le_csInf (Set.range_nonempty _) (by rintro y ⟨g,rfl⟩; exact hmin g)

theorem delta_nonnegative (v : ι → Circle) : 0 ≤ delta E v := by
  obtain ⟨gamma, hmin⟩ := exists_minimizer E v
  rw [delta_eq_minimum E v gamma hmin]
  exact edgeDefect_nonnegative E v gamma

/-- Compactness upgrades a zero infimum to an exact vertex gauge. -/
theorem delta_eq_zero_iff_hasVertexGauge (v : ι → Circle) :
    delta E v = 0 ↔ Resonance.HasVertexGauge E v := by
  constructor
  · intro hzero
    obtain ⟨gamma, hmin⟩ := exists_minimizer E v
    refine ⟨gamma, (edgeDefect_eq_zero_iff E v gamma).mp ?_⟩
    rw [← delta_eq_minimum E v gamma hmin]
    exact hzero
  · rintro ⟨gamma, hgamma⟩
    have hz := (edgeDefect_eq_zero_iff E v gamma).mpr hgamma
    have hmin : ∀ gamma', edgeDefect E v gamma ≤ edgeDefect E v gamma' := by
      intro gamma'
      rw [hz]
      exact edgeDefect_nonnegative E v gamma'
    rw [delta_eq_minimum E v gamma hmin, hz]

/-- The full zero-defect/cycle equivalence under the support-graph hypothesis. -/
theorem delta_eq_zero_iff_cycleResonant (v : ι → Circle)
    (root : ι) (hconn : Resonance.StronglyConnected E) :
    delta E v = 0 ↔ Resonance.CycleResonant E v := by
  exact (delta_eq_zero_iff_hasVertexGauge E v).trans
    (Resonance.cycleResonant_iff_hasVertexGauge v root hconn).symm

end NonSymmetricDyson.PhaseDefect
