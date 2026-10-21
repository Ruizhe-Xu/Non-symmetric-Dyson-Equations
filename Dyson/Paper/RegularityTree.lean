import Dyson.Paper.FoundationsTree
import Dyson.Full.MainRegularity
import Dyson.Paper.RegularityBounds
import Dyson.Paper.RegularityCompact

/-! Tree-backed M3 and revised M4, with exactly the source interval hypotheses and the
source's Euclidean uniform bound. M4 assumes a compact interval. -/
noncomputable section
open scoped Topology BigOperators ENNReal
open Set MeasureTheory
namespace NonSymmetricDyson.Paper.RegularityTree
open Full ExternalAlgebraic Full.Boundary Full.BoundaryMeasure Full.GlobalHolder
open Paper.Foundations
variable {n : ℕ}

/-- `thm.bound`: the closed interval may be unbounded. -/
theorem boundedness_of_solution
    (hn : 0 < n) (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (I : Set ℝ) (hclosed : IsClosed I) (hinterval : OrdConnected I) (Φ : ℝ)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im →
      Full.Norms.euclideanNorm (solution S a hS z) ≤ Φ) :
    ∃ c C β : ℝ, 0 < c ∧ 0 < C ∧ 0 < β ∧
      ∀ z ∈ closedStrip I,
        (∀ i, c / (1 + ‖z‖) ≤ ‖boundaryVector (solution S a hS) z i‖ ∧
          ‖boundaryVector (solution S a hS) z i‖ ≤ C / (1 + ‖z‖)) ∧
        (∀ i j, β * (boundaryVector (solution S a hS) z j).im ≤
          (boundaryVector (solution S a hS) z i).im ∧
          (boundaryVector (solution S a hS) z i).im ≤
          β⁻¹ * (boundaryVector (solution S a hS) z j).im) := by
  apply (RegularityBounds.main_theorem_three hn algebraic puiseux S a hS hirr (solution S a hS)
    (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz)
    (FoundationsTree.measure S a hn spectral unique hS) (fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).1)
    (fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).2.1) (sigma S a) (sigma_nonnegative S a)
    (fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).2.2.1) I Φ ?_).2
  intro z hzI hz i
  exact (norm_le_pi_norm _ i).trans ((Full.Norms.sup_le_euclidean _).trans (hbound z hzI hz))

/-- `thm.regularity` in the revision: I is a compact interval, the bound is
on the closed upper strip, and all three source conclusions are included. -/
theorem regularity_of_solution
    (hn : 0 < n) (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{0})
    (unique : TreeSpectral.ScalarStieltjesUniqueness)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion) (roots : RootHolderTheory)
    (glue : ExternalCompactHolderGluing (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (I : Set ℝ) (hcompact : IsCompact I) (hinterval : OrdConnected I) (Φ : ℝ)
    (hbound : ∀ z ∈ closedStrip I,
      Full.Norms.euclideanNorm (boundaryVector (solution S a hS) z) ≤ Φ) :
    (∀ i, (FoundationsTree.measure S a hn spectral unique hS i).restrict I =
      (volume.withDensity (fun x => ENNReal.ofReal (realDensity (solution S a hS) i x))).restrict I) ∧
    ∃ α C β : ℝ, 0 < α ∧ 0 < C ∧ 0 < β ∧
      (∀ i j x, x ∈ I → β * realDensity (solution S a hS) j x ≤
        realDensity (solution S a hS) i x ∧ realDensity (solution S a hS) i x ≤
        β⁻¹ * realDensity (solution S a hS) j x) ∧
      (∀ i x, x ∈ I → ∀ y, y ∈ I →
        |realDensity (solution S a hS) i x - realDensity (solution S a hS) i y| ≤
          C * |x - y| ^ α) ∧
      (∀ i z, z ∈ closedStrip I → ∀ w, w ∈ closedStrip I →
        ‖boundaryVector (solution S a hS) z i - boundaryVector (solution S a hS) w i‖ ≤
          C * ‖z - w‖ ^ α) := by
  have hbound' : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖solution S a hS z i‖ ≤ Φ := by
    intro z hzI hz i
    have hb := hbound z ⟨hzI,hz.le⟩
    rw [family_extension_agrees S a hS (solution S a hS)
      (fun z hz => solution_upper S a hS hz) (fun z hz => solution_equation S a hS hz) z hz] at hb
    exact (norm_le_pi_norm _ i).trans ((Full.Norms.sup_le_euclidean _).trans hb)
  let m := solution S a hS
  let μ := FoundationsTree.measure S a hn spectral unique hS
  have hu : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z) :=
    fun z hz => solution_upper S a hS hz
  have he : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z) :=
    fun z hz => solution_equation S a hS hz
  have hμ := fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).1
  have hrep := fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).2.1
  have hd : ∀ i, (μ i).restrict I =
      (volume.withDensity (fun x => ENNReal.ofReal (realDensity m i x))).restrict I :=
    fun i => family_restricted_density algebraic puiseux inversion S a hS m hu he
      μ hμ hrep I Φ hbound' i
  obtain ⟨_,c,C₀,β,hc,hC₀,hβ,hbounds⟩ := RegularityBounds.main_theorem_three
    hn algebraic puiseux S a hS hirr m hu he μ hμ hrep (sigma S a)
    (sigma_nonnegative S a) (fun i => (FoundationsTree.measure_spec S a hn spectral unique hS i).2.2.1) I Φ hbound'
  let M := max 0 Φ
  have hboundM : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M :=
    fun z hzI hz i => (hbound' z hzI hz i).trans (le_max_right _ _)
  obtain ⟨α,L,hα,hα1,hL,hm⟩ := RegularityCompact.dyson_compact_strip_holder
    glue algebraic puiseux roots S a hS m hu he I hcompact M (le_max_left _ _)
      hboundM μ hμ hrep
  have hv := density_holder (boundaryVector m) I α L hm
  have hcomp : ∀ i j x, x ∈ I → β * realDensity m j x ≤ realDensity m i x ∧
      realDensity m i x ≤ β⁻¹ * realDensity m j x := by
    intro i j x hx
    have h := (hbounds (x:ℂ) ⟨by simpa using hx, by simp⟩).2 i j
    constructor
    · simpa only [realDensity, mul_div_assoc] using div_le_div_of_nonneg_right h.1 Real.pi_pos.le
    · simpa only [realDensity, mul_div_assoc] using div_le_div_of_nonneg_right h.2 Real.pi_pos.le
  let C := max 1 (max L (L / Real.pi))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨hd,α,C,β,hα,hC,hβ,hcomp,?_,?_⟩
  · intro i x hx y hy
    exact (hv i x hx y hy).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (abs_nonneg _) _))
  · intro i z hz w hw
    exact (hm i z hz w hw).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg (norm_nonneg _) _))

end NonSymmetricDyson.Paper.RegularityTree
