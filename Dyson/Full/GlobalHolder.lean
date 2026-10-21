import Dyson.Full.BoundaryHolder
import Dyson.Full.MainBoundary
import Dyson.Full.StieltjesTails

/-! Uniform Hölder estimates on possibly unbounded closed vertical strips.
The external compact-cover lemma is generic for arbitrary finite families.
All high-height, real-tail, distant-pair and boundary-limit arguments are
internal, as are its applicability hypotheses for the Dyson solution. -/

noncomputable section
open scoped Topology
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.GlobalHolder

open Boundary ExternalAlgebraic
variable {ι : Type*} [Fintype ι]

def upperStrip (I : Set ℝ) : Set ℂ := {z | z.re ∈ I ∧ 0 < z.im}

def compactCore (I : Set ℝ) (σ : ℝ) : Set ℂ :=
  Metric.closedBall 0 (σ+4) ∩ closedStrip I

/-- Finite-family compact-cover/Lebesgue-number Hölder gluing. This is a
general theorem for arbitrary complex functions and arbitrary sets. -/
structure ExternalCompactHolderGluing (ι : Type*) [Fintype ι] : Prop where
  glue : ∀ (f : ℂ → ι → ℂ) (D K : Set ℂ), IsCompact K →
    (∀ i x, x ∈ K → LocalHolderOn (fun z => f z i) D x) →
    ∃ α C δ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ i z, z ∈ D → ∀ w, w ∈ D → z ∈ K → ‖z-w‖ < δ →
        ‖f z i-f w i‖ ≤ C * ‖z-w‖^α

theorem localHolder_mono {f : ℂ → ℂ} {D D' : Set ℂ} {x : ℂ}
    (h : LocalHolderOn f D x) (hsub : D' ⊆ D) : LocalHolderOn f D' x := by
  obtain ⟨α, C, r, hα, hα1, hC, hr, hh⟩ := h
  exact ⟨α, C, r, hα, hα1, hC, hr,
    fun z hz w hw => hh z (hsub hz) w (hsub hw)⟩

theorem isClosed_closedStrip {I : Set ℝ} (hI : IsClosed I) :
    IsClosed (closedStrip I) :=
  (hI.preimage Complex.continuous_re).inter
    (isClosed_le continuous_const Complex.continuous_im)

theorem compactCore_isCompact {I : Set ℝ} (hI : IsClosed I) (σ : ℝ) :
    IsCompact (compactCore I σ) :=
  (isCompact_closedBall (0 : ℂ) (σ+4)).inter_right (isClosed_closedStrip hI)

/-- The actual unbounded-strip gluing. Compactness is used only on the bounded
core; the remainder is covered by height and real-tail Lipschitz estimates. -/
theorem global_upper_holder (ext : ExternalCompactHolderGluing ι)
    (f : ℂ → ι → ℂ) (I : Set ℝ) (hI : IsClosed I) (σ M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ z ∈ upperStrip I, ∀ i, ‖f z i‖ ≤ M)
    (hlocal : ∀ i x, x ∈ compactCore I σ → LocalHolderOn (fun z => f z i) (upperStrip I) x)
    (hheight : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      1 ≤ z.im → 1 ≤ w.im → ‖f z i-f w i‖ ≤ ‖z-w‖)
    (htail : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      σ+1 ≤ |z.re| → σ+1 ≤ |w.re| → ‖f z i-f w i‖ ≤ ‖z-w‖) :
    ∃ α L : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ L ∧
      ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
        ‖f z i-f w i‖ ≤ L * ‖z-w‖^α := by
  obtain ⟨α, C, δ, hα, hα1, hC, hδ, hδ1, hnear⟩ :=
    ext.glue f (upperStrip I) (compactCore I σ) (compactCore_isCompact hI σ) hlocal
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
  · by_cases hzK : ‖z‖ ≤ σ+4
    · have hzcore : z ∈ compactCore I σ := ⟨by simpa using hzK, hz.1, hz.2.le⟩
      exact (hnear i z hz w hw hzcore hd).trans (mul_le_mul_of_nonneg_right hCL hp)
    · by_cases hwK : ‖w‖ ≤ σ+4
      · have hwcore : w ∈ compactCore I σ := ⟨by simpa using hwK, hw.1, hw.2.le⟩
        have hh := hnear i w hw z hz hwcore (by simpa only [norm_sub_rev] using hd)
        have hh' : ‖f z i-f w i‖ ≤ C * ‖z-w‖^α := by
          simpa only [norm_sub_rev] using hh
        exact hh'.trans (mul_le_mul_of_nonneg_right hCL hp)
      · apply hLip hd
        by_cases hh : 1 ≤ z.im ∧ 1 ≤ w.im
        · exact hheight i z hz w hw hh.1 hh.2
        · have him : |z.im-w.im| ≤ ‖z-w‖ := by
            simpa using Complex.abs_im_le_norm (z-w)
          have hdist : ‖z-w‖ < 1 := hd.trans_le hδ1
          have hsmall : z.im < 2 ∧ w.im < 2 := by
            have hab := abs_le.mp him
            rcases not_and_or.mp hh with hz' | hw'
            · have hz'' : z.im < 1 := lt_of_not_ge hz'
              constructor <;> linarith
            · have hw'' : w.im < 1 := lt_of_not_ge hw'
              constructor <;> linarith
          have hzt : σ+1 ≤ |z.re| := by
            have hn := Complex.norm_le_abs_re_add_abs_im z
            rw [abs_of_nonneg hz.2.le] at hn
            have hlarge := lt_of_not_ge hzK
            linarith
          have hwt : σ+1 ≤ |w.re| := by
            have hn := Complex.norm_le_abs_re_add_abs_im w
            rw [abs_of_nonneg hw.2.le] at hn
            have hlarge := lt_of_not_ge hwK
            linarith
          exact htail i z hz w hw hzt hwt
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

/-- A two-point upper-strip estimate passes to the actual continuous extension
by approaching both points at the same positive height. -/
theorem holder_pass_to_closed_strip
    (f F : ℂ → ℂ) (I : Set ℝ) (α L : ℝ)
    (hF : ContinuousOn F (closedStrip I))
    (hagrees : ∀ z ∈ upperStrip I, F z = f z)
    (hh : ∀ z ∈ upperStrip I, ∀ w ∈ upperStrip I,
      ‖f z-f w‖ ≤ L * ‖z-w‖^α) :
    ∀ z ∈ closedStrip I, ∀ w ∈ closedStrip I,
      ‖F z-F w‖ ≤ L * ‖z-w‖^α := by
  intro z hz w hw
  let lift (v : ℂ) (η : ℝ) : ℂ := v + (η : ℂ) * Complex.I
  have hlift (v : ℂ) (hv : v ∈ closedStrip I) {η : ℝ} (hη : 0 < η) :
      lift v η ∈ upperStrip I := by
    constructor
    · simpa [lift] using hv.1
    · simpa [lift] using add_pos_of_nonneg_of_pos hv.2 hη
  have hlim (v : ℂ) (hv : v ∈ closedStrip I) :
      Tendsto (fun η : ℝ => F (lift v η)) (𝓝[>] (0 : ℝ)) (𝓝 (F v)) := by
    apply (hF v hv).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (lift v) := by dsimp [lift]; fun_prop
      simpa [lift] using hc.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact ⟨(hlift v hv hη).1, (hlift v hv hη).2.le⟩
  apply le_of_tendsto ((hlim z hz).sub (hlim w hw)).norm
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hzη := hlift z hz hη
  have hwη := hlift w hw hη
  rw [hagrees _ hzη, hagrees _ hwη]
  have heq : lift z η - lift w η = z-w := by dsimp [lift]; ring
  simpa only [heq] using hh (lift z η) hzη (lift w η) hwη

/-- Full uniform coordinate Hölder estimate for the actual Dyson solution on
an arbitrary closed real set I, including unbounded intervals. -/
theorem dyson_closed_strip_holder (glue : ExternalCompactHolderGluing ι)
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (roots : RootHolderTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (I : Set ℝ) (hI : IsClosed I) (M σ : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, z.re ∈ I → 0 < z.im → ∀ i, ‖m z i‖ ≤ M)
    (μ : ι → Measure ℝ) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i))
    (hsupport : ∀ i, μ i (Icc (-σ) σ)ᶜ = 0) :
    ∃ α L : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ L ∧
      ∀ i z, z ∈ closedStrip I → ∀ w, w ∈ closedStrip I →
        ‖boundaryVector m z i-boundaryVector m w i‖ ≤ L * ‖z-w‖^α := by
  have hlocal : ∀ i x, x ∈ compactCore I σ →
      LocalHolderOn (fun z => m z i) (upperStrip I) x := by
    intro i x hx
    have ha := family_coordinate_analytic S a hS m hupper heq i
    apply localHolder_mono (D := upper) ?_ (fun z hz => hz.2)
    by_cases hxi : 0 < x.im
    · exact analyticAt_localHolder (ha x hxi) upper
    · have hx0 : x.im = 0 := le_antisymm (le_of_not_gt hxi) hx.2.2
      have hxreal : x = (x.re : ℂ) := Complex.ext (by simp) (by simpa using hx0)
      rw [hxreal]
      apply algebraic_localHolder_of_bounded puiseux roots (fun z => m z i) ha
        (solution_algebraic algebraic S a hS m hupper heq i)
        (fun z hz => hupper z hz i) x.re M
      intro η hη
      exact hbound (vertical x.re η) (by simpa [vertical] using hx.2.1)
        (by simpa using hη) i
  have hheight : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      1 ≤ z.im → 1 ≤ w.im → ‖m z i-m w i‖ ≤ ‖z-w‖ := by
    intro i z hz w hw hzi hwi
    letI := hμ i
    have hzrep : m z i = Poisson.stieltjes (μ i) z := hrep i z hz.2
    have hwrep : m w i = Poisson.stieltjes (μ i) w := hrep i w hw.2
    rw [hzrep, hwrep]
    exact StieltjesTails.stieltjes_upper_lipschitz (μ i) hzi hwi
  have htail : ∀ i z, z ∈ upperStrip I → ∀ w, w ∈ upperStrip I →
      σ+1 ≤ |z.re| → σ+1 ≤ |w.re| → ‖m z i-m w i‖ ≤ ‖z-w‖ := by
    intro i z hz w hw hzi hwi
    letI := hμ i
    have hzrep : m z i = Poisson.stieltjes (μ i) z := hrep i z hz.2
    have hwrep : m w i = Poisson.stieltjes (μ i) w := hrep i w hw.2
    rw [hzrep, hwrep]
    exact StieltjesTails.stieltjes_real_tail_lipschitz (μ i)
      (StieltjesTails.ae_abs_le_of_support (μ i) (hsupport i)) hzi hwi
  obtain ⟨α, L, hα, hα1, hL, hh⟩ := global_upper_holder glue m I hI σ M hM
    (fun z hz i => hbound z hz.1 hz.2 i) hlocal hheight htail
  refine ⟨α, L, hα, hα1, hL, ?_⟩
  intro i
  apply holder_pass_to_closed_strip (fun z => m z i) (fun z => boundaryVector m z i) I α L
  · exact (continuousOn_pi.mp
      (family_closedStrip_continuous algebraic puiseux S a hS m hupper heq I M hbound)) i
  · intro z hz
    exact extendFrom_extends
      (family_coordinate_analytic S a hS m hupper heq i).continuousOn z hz.2
  · exact hh i

/-- Taking real-boundary imaginary parts gives the density Hölder estimate,
with the explicit factor `1 / π`. -/
theorem density_holder (F : ℂ → ι → ℂ) (I : Set ℝ) (α L : ℝ)
    (hh : ∀ i z, z ∈ closedStrip I → ∀ w, w ∈ closedStrip I →
      ‖F z i-F w i‖ ≤ L * ‖z-w‖^α) :
    ∀ i x, x ∈ I → ∀ y, y ∈ I →
      |(F (x : ℂ) i).im / Real.pi - (F (y : ℂ) i).im / Real.pi| ≤
        (L / Real.pi) * |x-y|^α := by
  intro i x hx y hy
  have hx' : (x : ℂ) ∈ closedStrip I := ⟨by simpa using hx, by simp⟩
  have hy' : (y : ℂ) ∈ closedStrip I := ⟨by simpa using hy, by simp⟩
  have hb : ‖F (x : ℂ) i-F (y : ℂ) i‖ ≤ L * |x-y|^α := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      hh i (x : ℂ) hx' (y : ℂ) hy'
  have him : |(F (x : ℂ) i).im-(F (y : ℂ) i).im| ≤ ‖F (x : ℂ) i-F (y : ℂ) i‖ := by
    simpa using Complex.abs_im_le_norm (F (x : ℂ) i-F (y : ℂ) i)
  calc
    _ = |(F (x : ℂ) i).im-(F (y : ℂ) i).im| / Real.pi := by
      rw [← sub_div, abs_div, abs_of_pos Real.pi_pos]
    _ ≤ (L * |x-y|^α) / Real.pi :=
      div_le_div_of_nonneg_right (him.trans hb) Real.pi_pos.le
    _ = _ := by ring

end NonSymmetricDyson.Full.GlobalHolder
