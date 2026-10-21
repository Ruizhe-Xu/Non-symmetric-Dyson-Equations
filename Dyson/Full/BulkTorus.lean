import Dyson.PhaseDefect
import Mathlib

/-!
The only external input in this module is the generic metric error bound for
a continuous homomorphism of finite products of circles. It is a theorem of
finite-dimensional compact abelian Lie groups: write the homomorphism as an
integer matrix, use Smith normal form (including the nonprimitive invariant
factors), and invert each nonzero diagonal character locally; compactness
extends the estimate globally. Retaining every invariant factor preserves
all components of the kernel. This generic external theorem is assumed under
the user's explicit authorization of external arguments. The graph-specific
character map, its continuity, its kernel and the resulting resonance bound
are proved below; the external statement contains no graph or Dyson data.
-/

noncomputable section
open scoped Classical

namespace NonSymmetricDyson.Full.BulkTorus
universe u

def difference {I : Type*} (x y : I → Circle) : I → ℂ :=
  fun i => (x i : ℂ) - (y i : ℂ)

/-- External general finite-torus theorem; not a paper-specific assumption. -/
def FiniteTorusErrorBound : Prop :=
  ∀ {I J : Type u} [Fintype I] [Fintype J]
    (F : (I → Circle) →* (J → Circle)), Continuous F →
    ∃ C : ℝ, 0 < C ∧ ∀ x : I → Circle,
      ∃ y : I → Circle, F y = 1 ∧
        ‖difference x y‖ ≤ C * ‖difference (F x) 1‖

variable {V : Type u} [Fintype V] (E : V → V → Prop)

def graphCharacter : ((V ⊕ V) → Circle) →* (PhaseDefect.Edge E → Circle) where
  toFun x e := x (.inl e.val.1) * x (.inr e.val.1) * (x (.inr e.val.2))⁻¹
  map_one' := by funext e; simp
  map_mul' x y := by
    funext e
    simp [mul_comm, mul_left_comm, mul_assoc]

theorem graphCharacter_continuous : Continuous (graphCharacter E) := by
  apply continuous_pi
  intro e
  change Continuous (fun x : (V ⊕ V) → Circle =>
    x (.inl e.val.1) * x (.inr e.val.1) * (x (.inr e.val.2))⁻¹)
  fun_prop

theorem graphCharacter_kernel (x : (V ⊕ V) → Circle)
    (hx : graphCharacter E x = 1) :
    Resonance.HasVertexGauge E (fun i => x (.inl i)) := by
  refine ⟨fun i => x (.inr i), ?_⟩
  intro a b hab
  have he := congrFun hx (⟨(a,b), hab⟩ : PhaseDefect.Edge E)
  change x (.inl a) * x (.inr a) * (x (.inr b))⁻¹ = 1 at he
  have hm : x (.inl a) * x (.inr a) = x (.inr b) := by
    simpa using congrArg (fun z => z * x (.inr b)) he
  calc
    x (.inl a) = (x (.inr a))⁻¹ * (x (.inl a) * x (.inr a)) := by
      simp [mul_comm, mul_left_comm]
    _ = (x (.inr a))⁻¹ * x (.inr b) := by rw [hm]

theorem character_error_norm (u gamma : V → Circle) :
    ‖difference (graphCharacter E (Sum.elim u gamma)) 1‖ =
      PhaseDefect.edgeDefect E u gamma := by
  have heq (e : PhaseDefect.Edge E) :
      ‖difference (graphCharacter E (Sum.elim u gamma)) 1 e‖ =
        ‖PhaseDefect.edgeError E u gamma e‖ := by
    let a : ℂ := (u e.val.1 : ℂ)
    let b : ℂ := (gamma e.val.1 : ℂ)
    let c : ℂ := (gamma e.val.2 : ℂ)
    have hb : ‖b‖ = 1 := Circle.norm_coe _
    have hc : ‖c‖ = 1 := Circle.norm_coe _
    have hb0 : b ≠ 0 := by intro h; simp [h] at hb
    have hc0 : c ≠ 0 := by intro h; simp [h] at hc
    change ‖a * b * c⁻¹ - 1‖ = ‖a - b⁻¹ * c‖
    have hid : a * b * c⁻¹ - 1 = (a - b⁻¹ * c) * b * c⁻¹ := by
      field_simp
    rw [hid, norm_mul, norm_mul, norm_inv, hb, hc]
    simp
  unfold PhaseDefect.edgeDefect
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro e
    rw [heq]
    exact norm_le_pi_norm _ e
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro e
    rw [← heq]
    exact norm_le_pi_norm _ e

def resonanceDistance (u : V → Circle) : ℝ :=
  sInf {r : ℝ | ∃ v : V → Circle, Resonance.CycleResonant E v ∧
    r = ‖difference u v‖}

theorem resonanceDistance_nonnegative (u : V → Circle) :
    0 ≤ resonanceDistance E u := by
  apply le_csInf
  · refine ⟨‖difference u 1‖, 1, ?_, rfl⟩
    apply Resonance.cycleResonant_of_hasVertexGauge
    refine ⟨1, ?_⟩
    intro a b hab
    simp
  · rintro r ⟨v, hv, rfl⟩
    exact norm_nonneg _

theorem resonanceDistance_le (u v : V → Circle) (hv : Resonance.CycleResonant E v) :
    resonanceDistance E u ≤ ‖difference u v‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact norm_nonneg _
  · exact ⟨v, hv, rfl⟩

/-- The graph-specific metric estimate follows from the generic torus theorem
and the already proved gauge-to-cycle implication. -/
theorem distance_le_defect (external : FiniteTorusErrorBound.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : V → Circle,
      resonanceDistance E u ≤ C * PhaseDefect.delta E u := by
  obtain ⟨C, hC, hF⟩ := external (graphCharacter E)
    (graphCharacter_continuous E)
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨gamma, hmin⟩ := PhaseDefect.exists_minimizer E u
  obtain ⟨y, hy, hclose⟩ := hF (Sum.elim u gamma)
  let v : V → Circle := fun i => y (.inl i)
  have hv : Resonance.CycleResonant E v :=
    Resonance.cycleResonant_of_hasVertexGauge v (graphCharacter_kernel E y hy)
  have hcoord : ‖difference u v‖ ≤ ‖difference (Sum.elim u gamma) y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm (difference (Sum.elim u gamma) y) (.inl i)
  calc
    resonanceDistance E u ≤ ‖difference u v‖ := resonanceDistance_le E u v hv
    _ ≤ ‖difference (Sum.elim u gamma) y‖ := hcoord
    _ ≤ C * ‖difference (graphCharacter E (Sum.elim u gamma)) 1‖ := hclose
    _ = C * PhaseDefect.edgeDefect E u gamma := by rw [character_error_norm]
    _ = C * PhaseDefect.delta E u := by
      rw [PhaseDefect.delta_eq_minimum E u gamma hmin]

end NonSymmetricDyson.Full.BulkTorus
