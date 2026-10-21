import Dyson.Paper.RegularityProofs
import Dyson.Full.GlobalHolder

/-! The revised M4 compact-interval route: compactness on I × [0,2],
Puiseux two-point estimates near the real axis, and the derivative-based
Lipschitz estimate at height at least one. No real-tail argument is used. -/
noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace NonSymmetricDyson.Paper.RegularityCompact
open Full Full.Boundary Full.ExternalAlgebraic Full.GlobalHolder
variable {ι : Type*} [Fintype ι]

def slab (I : Set ℝ) : Set ℂ := {z | z.re ∈ I ∧ z.im ∈ Icc (0:ℝ) 2}

theorem slab_isCompact {I : Set ℝ} (hI : IsCompact I) : IsCompact (slab I) := by
  have he : slab I = (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*Complex.I) '' (I ×ˢ Icc (0:ℝ) 2) := by
    ext z
    constructor
    · intro hz
      exact ⟨(z.re,z.im), hz, by apply Complex.ext <;> simp⟩
    · rintro ⟨p,hp,rfl⟩
      simpa [slab] using hp
  rw [he]
  exact (hI.prod isCompact_Icc).image (by fun_prop)

/-- Compact near-axis estimates and upper-height estimates cover the strip. -/
theorem compact_upper_holder (ext : ExternalCompactHolderGluing ι)
    (f : ℂ → ι → ℂ) (I : Set ℝ) (hI : IsCompact I) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ z ∈ upperStrip I, ∀ i, ‖f z i‖ ≤ M)
    (hlocal : ∀ i x, x ∈ slab I → LocalHolderOn (fun z => f z i) (upperStrip I) x)
    (hheight : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      1 ≤ z.im → 1 ≤ w.im → ‖f z i-f w i‖ ≤ ‖z-w‖) :
    ∃ α L : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ L ∧
      ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
        ‖f z i-f w i‖ ≤ L * ‖z-w‖^α := by
  obtain ⟨α, C, δ, hα, hα1, hC, hδ, hδ1, hnear⟩ :=
    ext.glue f (upperStrip I) (slab I) (slab_isCompact hI) hlocal
  let L : ℝ := max C (max 1 (2*M / δ^α))
  have hCL : C ≤ L := le_max_left _ _
  have h1L : 1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hfarL : 2*M / δ^α ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hL : 0 ≤ L := zero_le_one.trans h1L
  refine ⟨α, L, hα, hα1, hL, ?_⟩
  intro i z hz w hw
  have hp : 0 ≤ ‖z-w‖^α := Real.rpow_nonneg (norm_nonneg _) _
  have hLip (hd : ‖z-w‖ < δ) (hlip : ‖f z i-f w i‖ ≤ ‖z-w‖) :
      ‖f z i-f w i‖ ≤ L * ‖z-w‖^α := by
    calc
      _ ≤ ‖z-w‖ := hlip
      _ ≤ ‖z-w‖^α := Real.self_le_rpow_of_le_one (norm_nonneg _) (hd.le.trans hδ1) hα1
      _ ≤ L * ‖z-w‖^α := by simpa using mul_le_mul_of_nonneg_right h1L hp
  by_cases hd : ‖z-w‖ < δ
  · by_cases hzK : z.im ≤ 2
    · have hzcore : z ∈ slab I := ⟨hz.1, hz.2.le, hzK⟩
      exact (hnear i z hz w hw hzcore hd).trans (mul_le_mul_of_nonneg_right hCL hp)
    · apply hLip hd
      have him : |z.im-w.im| ≤ ‖z-w‖ := by
        simpa using Complex.abs_im_le_norm (z-w)
      have hdist : ‖z-w‖ < 1 := hd.trans_le hδ1
      have hzi : 1 ≤ z.im := by linarith
      have hwi : 1 ≤ w.im := by linarith [le_abs_self (z.im-w.im)]
      exact hheight i z hz w hw hzi hwi
  · have hdist : δ ≤ ‖z-w‖ := le_of_not_gt hd
    have hpow : δ^α ≤ ‖z-w‖^α := Real.rpow_le_rpow hδ.le hdist hα.le
    have hδpow : 0 < δ^α := Real.rpow_pos_of_pos hδ α
    have hb : ‖f z i-f w i‖ ≤ 2*M := by
      have hn := norm_sub_le (f z i) (f w i)
      linarith [hbound z hz i, hbound w hw i]
    calc
      _ ≤ 2*M := hb
      _ = (2*M / δ^α) * δ^α := by field_simp [hδpow.ne']
      _ ≤ (2*M / δ^α) * ‖z-w‖^α :=
        mul_le_mul_of_nonneg_left hpow (div_nonneg (by positivity) hδpow.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfarL hp

theorem dyson_compact_strip_holder (glue : ExternalCompactHolderGluing ι)
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (roots : RootHolderTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (I : Set ℝ) (hI : IsCompact I) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i))
    :
    ∃ α L : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ L ∧
      ∀ i z, z ∈ closedStrip I → ∀ w, w ∈ closedStrip I →
        ‖boundaryVector m z i-boundaryVector m w i‖ ≤ L * ‖z-w‖^α := by
  have hlocal : ∀ i x, x ∈ slab I →
      LocalHolderOn (fun z => m z i) (upperStrip I) x := by
    intro i x hx
    have ha := family_coordinate_analytic S a hS m hupper heq i
    apply localHolder_mono (D := upper) ?_ (fun z hz => hz.2)
    by_cases hxi : 0 < x.im
    · exact analyticAt_localHolder (ha x hxi) upper
    · have hx0 : x.im = 0 := le_antisymm (le_of_not_gt hxi) hx.2.1
      have hxreal : x = (x.re : ℂ) := Complex.ext (by simp) (by simpa using hx0)
      rw [hxreal]
      apply algebraic_localHolder_of_bounded puiseux roots (fun z => m z i) ha
        (solution_algebraic algebraic S a hS m hupper heq i)
        (fun z hz => hupper z hz i) x.re M
      intro η hη
      exact hbound (vertical x.re η) (by simpa [vertical] using hx.1)
        (by simpa using hη) i
  have hheight : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      1 ≤ z.im → 1 ≤ w.im → ‖m z i-m w i‖ ≤ ‖z-w‖ := by
    intro i z hz w hw hzi hwi
    letI := hμ i
    have hzrep : m z i = Poisson.stieltjes (μ i) z := hrep i z hz.2
    have hwrep : m w i = Poisson.stieltjes (μ i) w := hrep i w hw.2
    rw [hzrep, hwrep]
    simpa using RegularityProofs.stieltjes_lipschitz_above_height (μ i) 1
      (by norm_num) z w hzi hwi
  obtain ⟨α, L, hα, hα1, hL, hh⟩ := compact_upper_holder glue m I hI M hM
    (fun z hz i => hbound z hz.1 hz.2 i) hlocal hheight
  refine ⟨α, L, hα, hα1, hL, ?_⟩
  intro i
  apply holder_pass_to_closed_strip (fun z => m z i) (fun z => boundaryVector m z i) I α L
  · exact (continuousOn_pi.mp
      (family_closedStrip_continuous algebraic puiseux S a hS m hupper heq I M hbound)) i
  · intro z hz
    exact extendFrom_extends
      (family_coordinate_analytic S a hS m hupper heq i).continuousOn z hz.2
  · exact hh i

end NonSymmetricDyson.Paper.RegularityCompact
