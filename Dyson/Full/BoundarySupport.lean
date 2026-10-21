import Dyson.Full.MainBoundary
import Dyson.Full.BoundaryTopology

/-! One-sided zero isolation for the actual convergent Puiseux expansion.
This is the analytic step needed for finite interval support; continuity
alone is never used to infer finitely many components. -/

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryTopology

/-- Away from the centre, the Laurent expression is an actual finite
boundary value. This identity is proved by taking full upper limits. -/
theorem PuiseuxChart.punctured_boundary_formula {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 0 < |x - τ| → |x - τ| < r →
      boundaryExtension f (x : ℂ) = p.root (x : ℂ) ^ p.exponent * p.factor (p.root (x : ℂ)) := by
  have hτ : (τ : ℂ) ∈ closedUpper := by simp
  have hr : Tendsto p.root (𝓝[closedUpper] (τ : ℂ)) (𝓝 0) := by
    simpa only [p.root_center] using (p.root_continuous _ hτ).tendsto
  obtain ⟨r, hrpos, hrt⟩ := Metric.mem_nhdsWithin_iff.mp
    (hr.eventually p.factor_analytic.eventually_analyticAt)
  refine ⟨min r p.radius, lt_min hrpos p.radius_pos, ?_⟩
  intro x hx hnear
  have hxupper : (x : ℂ) ∈ closedUpper := by simp
  have hdist : ‖(x : ℂ) - (τ : ℂ)‖ = |x - τ| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hfactor : AnalyticAt ℂ p.factor (p.root (x : ℂ)) :=
    hrt ⟨by simpa only [Metric.mem_ball, dist_eq_norm, hdist] using
      hnear.trans_le (min_le_left _ _), hxupper⟩
  have hrootne : p.root (x : ℂ) ≠ 0 := by
    intro hz
    have hp := p.root_power (x : ℂ) hxupper
    rw [hz, zero_pow (Nat.ne_of_gt p.denominator_pos)] at hp
    have he : (x : ℂ) = (τ : ℂ) := sub_eq_zero.mp hp.symm
    have he' : x = τ := Complex.ofReal_injective he
    simpa [he'] using hx
  have hrootlim : Tendsto p.root (𝓝[upper] (x : ℂ)) (𝓝 (p.root (x : ℂ))) :=
    ((p.root_continuous _ hxupper).mono
      (show upper ⊆ closedUpper from fun z hz => (show 0 < z.im from hz).le)).tendsto
  have hpower := (continuousAt_zpow₀ (p.root (x : ℂ)) p.exponent (Or.inl hrootne)).tendsto.comp hrootlim
  have hlim := hpower.mul (hfactor.continuousAt.tendsto.comp hrootlim)
  apply extendFrom_eq (real_mem_closure_upper x)
  apply hlim.congr'
  have hball : Metric.ball (τ : ℂ) p.radius ∈ 𝓝 (x : ℂ) :=
    Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball, dist_eq_norm, hdist] using
      (hnear.trans_le (min_le_right _ _)))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with z hz hznear
  exact (p.expansion z hz (by simpa only [Metric.mem_ball, dist_eq_norm] using hznear)).symm

def sideCoefficient (F : ℂ → ℂ) (k : ℤ) (c : ℂ) (s : ℝ) : ℝ :=
  (c ^ k * F ((s : ℂ) * c)).im

theorem sideCoefficient_analytic {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (k : ℤ) (c : ℂ) : AnalyticAt ℝ (sideCoefficient F k c) 0 := by
  have hlin : AnalyticAt ℝ (fun s : ℝ => (s : ℂ) * c) 0 :=
    (Complex.ofRealCLM.analyticAt 0).mul analyticAt_const
  have hinner : AnalyticAt ℝ (fun s : ℝ => F ((s : ℂ) * c)) 0 := by
    simpa using (hF.restrictScalars (𝕜 := ℝ)).comp_of_eq hlin (by simp)
  exact (Complex.imCLM.analyticAt _).comp (analyticAt_const.mul hinner)

theorem analytic_one_sided_zero_alternative {H : ℝ → ℝ} (hH : AnalyticAt ℝ H 0) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), H s = 0) ∨
      (∀ᶠ s in 𝓝[>] (0 : ℝ), H s ≠ 0) := by
  rcases hH.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exact Or.inl (hzero.filter_mono nhdsWithin_le_nhds)
  · apply Or.inr
    exact hne.filter_mono (nhdsWithin_mono _ (by
      intro s hs
      exact ne_of_gt hs))

end NonSymmetricDyson.Full.Boundary

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryTopology

theorem finite_avoid_right {A : Set ℝ} (hA : A.Finite) (τ : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), τ + r ∉ A := by
  have hdiff : (A \ {τ}).Finite := hA.diff
  have hN : (A \ {τ})ᶜ ∈ 𝓝 τ :=
    hdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  have ht : Tendsto (fun r : ℝ => τ + r) (𝓝[>] (0 : ℝ)) (𝓝 τ) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))))
  filter_upwards [ht.eventually hN, self_mem_nhdsWithin] with r hr hpos
  have hp : 0 < r := hpos
  intro ha
  apply hr
  exact ⟨ha, by simp only [Set.mem_singleton_iff]; linarith⟩

theorem finite_avoid_left {A : Set ℝ} (hA : A.Finite) (τ : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), τ - r ∉ A := by
  have hdiff : (A \ {τ}).Finite := hA.diff
  have hN : (A \ {τ})ᶜ ∈ 𝓝 τ :=
    hdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  have ht : Tendsto (fun r : ℝ => τ - r) (𝓝[>] (0 : ℝ)) (𝓝 τ) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))))
  filter_upwards [ht.eventually hN, self_mem_nhdsWithin] with r hr hpos
  have hp : 0 < r := hpos
  intro ha
  apply hr
  exact ⟨ha, by simp only [Set.mem_singleton_iff]; linarith⟩

theorem right_interval_of_eventual {P : ℝ → Prop} {τ : ℝ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (τ + r)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Ioo τ (τ + R), P x := by
  obtain ⟨R, hR, hh⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hp : 0 < x - τ := by linarith [hx.1]
  have hsmall : x - τ < R := by linarith [hx.2]
  have h := hh (show x - τ ∈ Metric.ball 0 R ∩ Ioi 0 from
    ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hp] using hsmall, hp⟩)
  simpa using h

theorem left_interval_of_eventual {P : ℝ → Prop} {τ : ℝ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (τ - r)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ Ioo (τ - R) τ, P x := by
  obtain ⟨R, hR, hh⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hp : 0 < τ - x := by linarith [hx.2]
  have hsmall : τ - x < R := by linarith [hx.1]
  have h := hh (show τ - x ∈ Metric.ball 0 R ∩ Ioi 0 from
    ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hp] using hsmall, hp⟩)
  simpa using h

theorem oneSidedConstantNear_of_eventual {U : Set ℝ} {τ : ℝ}
    (hl : (∀ᶠ r in 𝓝[>] (0 : ℝ), τ-r ∈ U) ∨ (∀ᶠ r in 𝓝[>] (0 : ℝ), τ-r ∉ U))
    (hr : (∀ᶠ r in 𝓝[>] (0 : ℝ), τ+r ∈ U) ∨ (∀ᶠ r in 𝓝[>] (0 : ℝ), τ+r ∉ U)) :
    OneSidedConstantNear U τ := by
  have hleft : ∃ L : ℝ, 0 < L ∧ (Ioo (τ-L) τ ⊆ U ∨ Ioo (τ-L) τ ⊆ Uᶜ) := by
    rcases hl with hl | hl
    · obtain ⟨L, hL, hh⟩ := left_interval_of_eventual hl
      exact ⟨L, hL, Or.inl hh⟩
    · obtain ⟨L, hL, hh⟩ := left_interval_of_eventual (P := fun x => x ∉ U) (τ := τ) hl
      exact ⟨L, hL, Or.inr hh⟩
  have hright : ∃ R : ℝ, 0 < R ∧ (Ioo τ (τ+R) ⊆ U ∨ Ioo τ (τ+R) ⊆ Uᶜ) := by
    rcases hr with hr | hr
    · obtain ⟨R, hR, hh⟩ := right_interval_of_eventual hr
      exact ⟨R, hR, Or.inl hh⟩
    · obtain ⟨R, hR, hh⟩ := right_interval_of_eventual (P := fun x => x ∉ U) (τ := τ) hr
      exact ⟨R, hR, Or.inr hh⟩
  obtain ⟨L, hL, hl⟩ := hleft
  obtain ⟨R, hR, hr⟩ := hright
  refine ⟨min L R, lt_min hL hR, ?_, ?_⟩
  · have hsub : Ioo (τ - min L R) τ ⊆ Ioo (τ-L) τ := by
      intro x hx
      exact ⟨by linarith [min_le_left L R, hx.1], hx.2⟩
    exact hl.imp (fun h => hsub.trans h) (fun h => hsub.trans h)
  · have hsub : Ioo τ (τ + min L R) ⊆ Ioo τ (τ+R) := by
      intro x hx
      exact ⟨hx.1, by linarith [min_le_right L R, hx.2]⟩
    exact hr.imp (fun h => hsub.trans h) (fun h => hsub.trans h)

end NonSymmetricDyson.Full.Boundary

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

theorem PuiseuxChart.side_zero_alternative {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) (θ : ℝ) (hθ : θ = 0 ∨ θ = Real.pi) :
    (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryExtension f (ray τ r θ)).im = 0) ∨
      (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryExtension f (ray τ r θ)).im ≠ 0) := by
  let α : ℝ := 1 / (p.denominator : ℝ)
  let c : ℂ := Complex.exp (((θ / (p.denominator : ℝ) : ℝ) : ℂ) * Complex.I)
  let s : ℝ → ℝ := fun r => r ^ α
  have hα : 0 < α := div_pos zero_lt_one (by exact_mod_cast p.denominator_pos)
  have hθI : θ ∈ Icc (0 : ℝ) Real.pi := by
    rcases hθ with rfl | rfl <;> constructor <;> linarith [Real.pi_pos]
  have hspos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < s r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact Real.rpow_pos_of_pos hr α
  have hst : Tendsto s (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hspos⟩
    simpa only [s, Real.zero_rpow (ne_of_gt hα)] using
      (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hform : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (boundaryExtension f (ray τ r θ)).im =
        (s r) ^ p.exponent * sideCoefficient p.factor p.exponent c (s r) := by
    obtain ⟨R, hR, hformula⟩ := PuiseuxChart.punctured_boundary_formula p
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R :=
      (gt_mem_nhds hR).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    have hrpos : 0 < r := hr
    have hb : boundaryExtension f (ray τ r θ) =
        p.root (ray τ r θ) ^ p.exponent * p.factor (p.root (ray τ r θ)) := by
      rcases hθ with hθ | hθ
      · subst θ
        have h := hformula (τ + r) (by simpa using (ne_of_gt hrpos)) (by simpa [abs_of_pos hrpos] using hrR)
        simpa [ray, Complex.ofReal_add] using h
      · subst θ
        have h := hformula (τ - r) (by simpa using (ne_of_gt hrpos)) (by simpa [abs_of_pos hrpos] using hrR)
        simpa [ray, Complex.exp_pi_mul_I, Complex.ofReal_sub, sub_eq_add_neg] using h
    rw [hb, p.root_ray r θ hr hθI, mul_zpow]
    change (((s r : ℝ) : ℂ) ^ p.exponent * c ^ p.exponent *
      p.factor ((s r : ℂ) * c)).im = _
    rw [mul_assoc, ← Complex.ofReal_zpow]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      sideCoefficient]
  rcases analytic_one_sided_zero_alternative
    (sideCoefficient_analytic p.factor_analytic p.exponent c) with hz | hn
  · apply Or.inl
    filter_upwards [hform, hst.eventually hz] with r hformr hzr
    rw [hformr, hzr, mul_zero]
  · apply Or.inr
    filter_upwards [hform, hst.eventually hn, hspos] with r hformr hnr hsr
    rw [hformr]
    exact mul_ne_zero (ne_of_gt (zpow_pos hsr _)) hnr

end NonSymmetricDyson.Full.Boundary
namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic BoundaryTopology

variable {ι : Type*} [Fintype ι]

theorem family_regularSupport_open
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i : ι) :
    IsOpen (regularSupport m i) := by
  have hfin := family_singular_finite algebraic puiseux S a hS m hupper heq
  have hcont := continuousOn_pi.mp
    (family_boundary_continuous algebraic puiseux S a hS m hupper heq) i
  have hreal : ContinuousOn (fun x : ℝ => (boundaryVector m (x : ℂ) i).im)
      (singularUnion m)ᶜ := by
    apply Complex.continuous_im.comp_continuousOn
    exact hcont.comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨x, hx, rfl⟩)
  exact hreal.isOpen_inter_preimage hfin.isClosed.isOpen_compl isOpen_Ioi

theorem family_regularSupport_one_sided
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i : ι) (τ : ℝ) :
    OneSidedConstantNear (regularSupport m i) τ := by
  have hI : Complex.I ∈ upper := by simp
  have hnonzero : m Complex.I i ≠ 0 := BasicEstimates.component_ne_zero (hupper _ hI) i
  obtain ⟨_, hcharts⟩ := puiseux (fun z => m z i)
    (family_coordinate_analytic S a hS m hupper heq i)
    (solution_algebraic algebraic S a hS m hupper heq i) ⟨Complex.I, hI, hnonzero⟩
  obtain ⟨p⟩ := hcharts τ
  have hfin := family_singular_finite algebraic puiseux S a hS m hupper heq
  have hnonneg (x : ℝ) (hx : x ∉ singularUnion m) :
      0 ≤ (boundaryVector m (x : ℂ) i).im :=
    (family_boundary_equation algebraic puiseux S a hS m hupper heq x hx).2.1 i
  have hleft :
      (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryVector m ((τ-r : ℝ) : ℂ) i).im = 0) ∨
      (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryVector m ((τ-r : ℝ) : ℂ) i).im ≠ 0) := by
    simpa [boundaryVector, ray, Complex.exp_pi_mul_I, Complex.ofReal_sub, sub_eq_add_neg] using
      PuiseuxChart.side_zero_alternative p Real.pi (Or.inr rfl)
  have hright :
      (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryVector m ((τ+r : ℝ) : ℂ) i).im = 0) ∨
      (∀ᶠ r in 𝓝[>] (0 : ℝ), (boundaryVector m ((τ+r : ℝ) : ℂ) i).im ≠ 0) := by
    simpa [boundaryVector, ray, Complex.ofReal_add] using
      PuiseuxChart.side_zero_alternative p 0 (Or.inl rfl)
  apply oneSidedConstantNear_of_eventual
  · rcases hleft with hz | hn
    · apply Or.inr
      filter_upwards [hz] with r hr
      intro hs
      exact (ne_of_gt hs.2) hr
    · apply Or.inl
      filter_upwards [hn, finite_avoid_left hfin τ] with r hr hnot
      exact ⟨hnot, lt_of_le_of_ne (hnonneg _ hnot) (Ne.symm hr)⟩
  · rcases hright with hz | hn
    · apply Or.inr
      filter_upwards [hz] with r hr
      intro hs
      exact (ne_of_gt hs.2) hr
    · apply Or.inl
      filter_upwards [hn, finite_avoid_right hfin τ] with r hr hnot
      exact ⟨hnot, lt_of_le_of_ne (hnonneg _ hnot) (Ne.symm hr)⟩

end NonSymmetricDyson.Full.Boundary

