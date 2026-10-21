import Dyson.Full.BoundaryBounds
import Dyson.Full.GlobalHolder

/-! M4: absolute continuity of the restriction, comparable boundary
densities, and uniform Hölder regularity on the complete closed strip.
The interval may be unbounded. -/

noncomputable section
open scoped Topology BigOperators ENNReal
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryMeasure Foundations GlobalHolder

def realDensity {ι : Type*} (m : ℂ → ι → ℂ) (i : ι) (x : ℝ) : ℝ :=
  (boundaryVector m (x : ℂ) i).im / Real.pi

theorem family_restricted_density {ι : Type*} [Fintype ι]
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (I : Set ℝ) (M : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M) (i : ι) :
    (μ i).restrict I = (densityMeasure (fun z => boundaryVector m z i)).restrict I := by
  let U : Set ℝ := (singularUnion m)ᶜ
  have hfinite := family_singular_finite algebraic puiseux S a hS m hupper heq
  have hU : IsOpen U := hfinite.isClosed.isOpen_compl
  have hcont : ContinuousOn (fun z => boundaryVector m z i) (boundaryDomain U) :=
    continuousOn_pi.mp (family_boundary_continuous algebraic puiseux S a hS m hupper heq) i
  have hrestrict := inversion.inversion (μ i) (fun z => m z i)
    (fun z => boundaryVector m z i) U (hμ i) (hrep i) hU hcont
    (fun z hz => congrFun (family_extension_agrees S a hS m hupper heq z hz) i)
  have hsub : I ⊆ U := fun τ hτ => strip_disjoint_singular m I M hbound τ hτ
  rw [← Measure.restrict_restrict_of_subset hsub, hrestrict,
    Measure.restrict_restrict_of_subset hsub]

/-- Full initial regularity theorem, with actual density measures and
uniform two-point inequalities for all heights and unbounded real tails. -/
theorem main_theorem_four {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion) (roots : RootHolderTheory)
    (glue : ExternalCompactHolderGluing (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Fin n → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Represents (fun z => m z i) (μ i))
    (σ : ℝ) (hσ : 0 ≤ σ) (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0)
    (I : Set ℝ) (hI : IsClosed I) (Φ : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ Φ) :
    (∀ i, (μ i).restrict I =
      (volume.withDensity (fun x => ENNReal.ofReal (realDensity m i x))).restrict I) ∧
    ∃ α L β : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ L ∧ 0 < β ∧
      (∀ i z, z ∈ closedStrip I → ∀ w, w ∈ closedStrip I →
        ‖boundaryVector m z i - boundaryVector m w i‖ ≤ L * ‖z - w‖ ^ α) ∧
      (∀ i x, x ∈ I → ∀ y, y ∈ I →
        |realDensity m i x - realDensity m i y| ≤ (L / Real.pi) * |x - y| ^ α) ∧
      (∀ i j x, x ∈ I → β * realDensity m j x ≤ realDensity m i x ∧
        realDensity m i x ≤ β⁻¹ * realDensity m j x) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact family_restricted_density algebraic puiseux inversion S a hS m hupper heq
      μ hμ hrep I Φ hbound i
  · obtain ⟨_, c, C, β, hc, hC, hβ, hbounds⟩ := main_theorem_three hn algebraic puiseux
      S a hS hirr m hupper heq μ hμ hrep σ hσ hsupport I Φ hbound
    let M : ℝ := max 0 Φ
    have hM : 0 ≤ M := le_max_left _ _
    have hboundM : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M :=
      fun z hzI hz i => (hbound z hzI hz i).trans (le_max_right _ _)
    obtain ⟨α, L, hα, hα1, hL, hholder⟩ := dyson_closed_strip_holder glue algebraic puiseux roots
      S a hS m hupper heq I hI M σ hM hboundM μ hμ hrep hsupport
    refine ⟨α, L, β, hα, hα1, hL, hβ, hholder,
      density_holder (boundaryVector m) I α L hholder, ?_⟩
    intro i j x hx
    have hxstrip : (x : ℂ) ∈ closedStrip I := ⟨by simpa using hx, by simp⟩
    have h := (hbounds (x : ℂ) hxstrip).2 i j
    constructor
    · simpa only [realDensity, mul_div_assoc] using
        div_le_div_of_nonneg_right h.1 Real.pi_pos.le
    · simpa only [realDensity, mul_div_assoc] using
        div_le_div_of_nonneg_right h.2 Real.pi_pos.le

end NonSymmetricDyson.Full.Boundary
