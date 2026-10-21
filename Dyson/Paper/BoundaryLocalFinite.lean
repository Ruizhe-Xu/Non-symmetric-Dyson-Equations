import Dyson.Full.BoundarySupport
import Dyson.Full.BoundaryExterior

/-! The source's local-isolation and compact-cover proof of finite
singularities, using only the local Puiseux charts and the proved spectral
support bound. The finite exceptional-set part of algebraic function theory
is not used by these declarations. -/
noncomputable section
open scoped Topology
open Filter Set MeasureTheory
namespace NonSymmetricDyson.Paper.BoundaryLocalFinite
open Full Full.Boundary Full.ExternalAlgebraic

theorem chart_punctured_finite_limits {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 0 < |x-τ| → |x-τ| < r →
      ∃ b : ℂ, Tendsto (fun η => f (Full.Boundary.vertical x η)) (𝓝[>] (0:ℝ)) (𝓝 b) := by
  have hτ : (τ:ℂ) ∈ closedUpper := by simp
  have hr : Tendsto p.root (𝓝[closedUpper] (τ:ℂ)) (𝓝 0) := by
    simpa only [p.root_center] using (p.root_continuous _ hτ).tendsto
  obtain ⟨r,hrpos,hrt⟩ := Metric.mem_nhdsWithin_iff.mp
    (hr.eventually p.factor_analytic.eventually_analyticAt)
  refine ⟨min r p.radius,lt_min hrpos p.radius_pos,?_⟩
  intro x hx hnear
  have hxupper : (x:ℂ) ∈ closedUpper := by simp
  have hdist : ‖(x:ℂ)-(τ:ℂ)‖ = |x-τ| := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hfactor : AnalyticAt ℂ p.factor (p.root (x:ℂ)) :=
    hrt ⟨by simpa only [Metric.mem_ball,dist_eq_norm,hdist] using
      hnear.trans_le (min_le_left _ _),hxupper⟩
  have hnz : p.root (x:ℂ) ≠ 0 := by
    intro hz
    have hp := p.root_power (x:ℂ) hxupper
    rw [hz,zero_pow (Nat.ne_of_gt p.denominator_pos)] at hp
    have he : x=τ := Complex.ofReal_injective (sub_eq_zero.mp hp.symm)
    simpa [he] using hx
  have hrootlim : Tendsto p.root (𝓝[upper] (x:ℂ)) (𝓝 (p.root (x:ℂ))) :=
    ((p.root_continuous _ hxupper).mono
      (show upper ⊆ closedUpper from fun z hz => (show 0 < z.im from hz).le)).tendsto
  have hpower := (continuousAt_zpow₀ (p.root (x:ℂ)) p.exponent (Or.inl hnz)).tendsto.comp hrootlim
  have hlim := hpower.mul (hfactor.continuousAt.tendsto.comp hrootlim)
  have hf : Tendsto f (𝓝[upper] (x:ℂ))
      (𝓝 (p.root (x:ℂ)^p.exponent*p.factor (p.root (x:ℂ)))) := by
    apply hlim.congr'
    have hball : Metric.ball (τ:ℂ) p.radius ∈ 𝓝 (x:ℂ) :=
      Metric.isOpen_ball.mem_nhds (by simpa only [Metric.mem_ball,dist_eq_norm,hdist] using
        (hnear.trans_le (min_le_right _ _)))
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds hball] with z hz hznear
    exact (p.expansion z hz (by simpa only [Metric.mem_ball,dist_eq_norm] using hznear)).symm
  refine ⟨_,hf.comp ?_⟩
  exact tendsto_nhdsWithin_iff.mpr ⟨vertical_tendsto x,vertical_eventually_upper x⟩

theorem chart_isolates_singularities {f : ℂ → ℂ} {τ : ℝ}
    (p : PuiseuxChart f τ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ singularSet f, x ∈ Ioo (τ-r) (τ+r) → x=τ := by
  obtain ⟨r,hr,hlim⟩ := chart_punctured_finite_limits p
  refine ⟨r,hr,?_⟩
  intro x hx hnear
  by_contra hne
  obtain ⟨b,hb⟩ := hlim x (abs_pos.mpr (sub_ne_zero.mpr hne))
    (abs_lt.mpr ⟨by linarith [hnear.1],by linarith [hnear.2]⟩)
  exact not_tendsto_atTop_of_tendsto_nhds hb.norm hx

theorem finite_of_local_isolation {Y K : Set ℝ} (hK : IsCompact K) (hYK : Y ⊆ K)
    (hlocal : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ Y, y ∈ Ioo (x-r) (x+r) → y=x) : Y.Finite := by
  classical
  choose r hr hi using fun x : K => hlocal x x.property
  have hcover : K ⊆ ⋃ x : K, Ioo (x.val-r x) (x.val+r x) := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x,hx⟩,?_⟩
    constructor <;> dsimp <;> linarith [hr ⟨x,hx⟩]
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover
    (fun x : K => Ioo (x.val-r x) (x.val+r x)) (fun _ => isOpen_Ioo) hcover
  apply (T.finite_toSet.image (fun x : K => x.val)).subset
  intro y hy
  obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hT (hYK hy))
  exact ⟨x,hx,(hi x y hy hxy).symm⟩

/-- Singularities lie in the spectral interval; local Puiseux isolation
and a finite subcover prove that there are only finitely many. -/
theorem singular_finite_from_local_charts (f : ℂ → ℂ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (σ : ℝ) (hs : μ (Icc (-σ) σ)ᶜ=0)
    (hrep : Foundations.Represents f μ) (charts : ∀ τ : ℝ, Nonempty (PuiseuxChart f τ)) :
    (singularSet f).Finite := by
  apply finite_of_local_isolation isCompact_Icc (singularSet_subset_support_interval μ f hs hrep)
  intro τ _
  obtain ⟨p⟩ := charts τ
  exact chart_isolates_singularities p

end NonSymmetricDyson.Paper.BoundaryLocalFinite
