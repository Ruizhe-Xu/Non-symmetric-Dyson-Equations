import Dyson.Full.PoissonDensity
import Dyson.Full.MainDecomposition
import Dyson.Full.SingularitiesDensityClassification

/-! Actual local measure restrictions and changes of origin/orientation for
the manuscript's Poisson-kernel proof. Remote mass, including atoms, remains
in the probability measure; it is not silently discarded. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Classical

namespace NonSymmetricDyson.Paper.PoissonMeasureBridge
open Full Boundary BoundaryMeasure Foundations

theorem map_withDensity_equiv (e : ℝ ≃ᵐ ℝ) (ν : Measure ℝ) (f : ℝ → ℝ≥0∞) :
    (ν.withDensity f).map e = (ν.map e).withDensity (fun x => f (e.symm x)) := by
  ext A hA
  rw [e.map_apply, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA, e.restrict_map, e.measurableEmbedding.lintegral_map]
  simp

def translation (τ : ℝ) : ℝ ≃ᵐ ℝ where
  toFun x := x-τ
  invFun x := x+τ
  left_inv x := by ring
  right_inv x := by ring
  measurable_toFun := measurable_id.sub_const τ
  measurable_invFun := measurable_id.add_const τ

def reflection : ℝ ≃ᵐ ℝ where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  measurable_toFun := measurable_id.neg
  measurable_invFun := measurable_id.neg

theorem translation_volume (τ : ℝ) : (volume : Measure ℝ).map (translation τ)=volume := by
  change volume.map (fun x : ℝ => x-τ)=volume
  simpa only [sub_eq_add_neg] using map_add_right_eq_self volume (-τ)

theorem reflection_volume : (volume : Measure ℝ).map reflection=volume := by
  exact Measure.map_neg_eq_self volume

theorem density_map_restriction (e : ℝ ≃ᵐ ℝ)
    (he : (volume : Measure ℝ).map e=volume)
    (μ : Measure ℝ) (v : ℝ → ℝ) (A : Set ℝ)
    (hμ : μ.restrict (e ⁻¹' A) =
      (volume.restrict (e ⁻¹' A)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (μ.map e).restrict A =
      (volume.restrict A).withDensity (fun x => ENNReal.ofReal (v (e.symm x))) := by
  rw [e.restrict_map, hμ, map_withDensity_equiv, ← e.restrict_map, he]

/-- A local continuous density is replaced by a globally measurable
nonnegative representative, agreeing at every point in the local window. -/
theorem measurable_density_representative (A : Set ℝ) (hA : MeasurableSet A)
    (v : ℝ → ℝ) (hv : ContinuousOn v A) (hn : ∀ x ∈ A, 0 ≤ v x) :
    ∃ w : ℝ → ℝ, Measurable w ∧ (∀ x, 0 ≤ w x) ∧ (∀ x ∈ A, w x=v x) := by
  let w := A.piecewise v (fun _ => 0)
  refine ⟨w, hv.measurable_piecewise continuousOn_const hA, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ A
    · simpa [w, hx] using hn x hx
    · simp [w, hx]
  · intro x hx
    simp [w, hx]

variable {ι : Type*} [Fintype ι]

/-- Stieltjes inversion applied on an actual interval free of the previously
proved singular set. This supplies the local density identity used in M6. -/
theorem actual_local_density
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := ι))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (i : ι)
    (hrep : Represents (fun z => m z i) μ)
    (U : Set ℝ) (hU : IsOpen U) (hregular : ∀ x ∈ U, x ∉ singularUnion m) :
    μ.restrict U = (volume.restrict U).withDensity
      (fun x => ENNReal.ofReal (realDensity m i x)) := by
  have hc : ContinuousOn (fun z => boundaryVector m z i) (boundaryDomain U) := by
    apply ((continuous_apply i).comp_continuousOn
      (family_boundary_continuous algebraic puiseux S a hS m hupper heq)).mono
    rintro z (hz | ⟨x,hx,rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨x,hregular x hx,rfl⟩
  have ha : ∀ z : ℂ, 0 < z.im → boundaryVector m z i=m z i := by
    intro z hz
    exact congrFun (family_extension_agrees S a hS m hupper heq z hz) i
  have hh := inversion.inversion μ (fun z => m z i) (fun z => boundaryVector m z i)
    U hμ hrep hU hc ha
  rw [hh]
  exact restrict_withDensity hU.measurableSet _

/-- Both translation and reflection use this single exact local-measure
identity. The transformed density is globally measurable and nonnegative. -/
theorem actual_transformed_local_density
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := ι))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (i : ι)
    (hrep : Represents (fun z => m z i) μ)
    (e : ℝ ≃ᵐ ℝ) (he : (volume : Measure ℝ).map e=volume)
    (hc : Continuous e) (hi : Continuous e.symm)
    (A : Set ℝ) (hA : IsOpen A)
    (hregular : ∀ x ∈ A, e.symm x ∉ singularUnion m) :
    ∃ v : ℝ → ℝ, Measurable v ∧ (∀ x, 0 ≤ v x) ∧
      (∀ x ∈ A, v x=realDensity m i (e.symm x)) ∧
      (μ.map e).restrict A =
        (volume.restrict A).withDensity (fun x => ENNReal.ofReal (v x)) := by
  have hr : ∀ x ∈ e ⁻¹' A, x ∉ singularUnion m := by
    intro x hx
    simpa using hregular (e x) hx
  have hlocal := actual_local_density algebraic puiseux inversion S a hS m hupper heq
    μ hμ i hrep (e ⁻¹' A) (hA.preimage hc) hr
  have hmapped := density_map_restriction e he μ (realDensity m i) A hlocal
  have hb : ContinuousOn (fun x => boundaryVector m ((e.symm x : ℝ) : ℂ) i) A := by
    apply ((continuous_apply i).comp_continuousOn
      (family_boundary_continuous algebraic puiseux S a hS m hupper heq)).comp
        (Complex.continuous_ofReal.comp hi).continuousOn
    intro x hx
    exact Or.inr ⟨e.symm x,hregular x hx,rfl⟩
  have hv : ContinuousOn (fun x => realDensity m i (e.symm x)) A :=
    (Complex.continuous_im.comp_continuousOn hb).div_const Real.pi
  have hn : ∀ x ∈ A, 0 ≤ realDensity m i (e.symm x) := by
    intro x hx
    exact div_nonneg ((family_boundary_equation algebraic puiseux S a hS m hupper heq
      (e.symm x) (hregular x hx)).2.1 i) Real.pi_pos.le
  obtain ⟨v,hv,hn,heqv⟩ := measurable_density_representative A hA.measurableSet _ hv hn
  refine ⟨v,hv,hn,heqv,hmapped.trans ?_⟩
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
  rw [heqv x hx]

theorem restrict_density_to_support (v : ℝ → ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A)
    (hz : ∀ x ∈ A, x ∉ B → v x=0) :
    (volume.restrict A).withDensity (fun x => ENNReal.ofReal (v x)) =
      (volume.restrict B).withDensity (fun x => ENNReal.ofReal (v x)) := by
  rw [← withDensity_indicator hA, ← withDensity_indicator hB]
  congr 1
  funext x
  by_cases hxB : x ∈ B
  · simp [hxB,hBA hxB]
  · by_cases hxA : x ∈ A
    · simp [hxA,hxB,hz x hxA hxB]
    · simp [hxA,hxB]

theorem edge_half_window (v : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hz : ∀ x ∈ Ioo (-r) r, x ≤ 0 → v x=0) :
    (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x)) =
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x)) := by
  apply restrict_density_to_support v _ _ measurableSet_Ioo measurableSet_Ioo
  · intro x hx
    exact ⟨by linarith [hx.1],hx.2⟩
  · intro x hx hn
    apply hz x hx
    by_contra hp
    exact hn ⟨lt_of_not_ge hp,hx.2⟩

theorem quadratic_error_comparison {v D C t : ℝ}
    (ht : 0 ≤ t) (hsmall : C*t ≤ D/2) (herror : |v-D*t| ≤ C*t^2) :
    (D/2)*t ≤ v ∧ v ≤ (3*D/2)*t := by
  have h := abs_le.mp herror
  have hm := mul_le_mul_of_nonneg_right hsmall ht
  constructor <;> nlinarith

theorem rootRadius_factor (c : ℝ) (k : ℕ) (x : ℝ) :
    Singularities.rootRadius c k x = |x| ^ ((k:ℝ)⁻¹) / |c| ^ ((k:ℝ)⁻¹) := by
  exact Real.div_rpow (abs_nonneg x) (abs_nonneg c) _

/-- Quantitative comparison obtained from the actual second-order asymptotic
remainder. No density power bound is supplied as an additional assumption. -/
theorem root_asymptotic_comparison (v : ℝ → ℝ) (τ c D C : ℝ) (k : ℕ)
    (hc : c ≠ 0) (hD : 0 < D) (hk : 0 < k) (P : ℝ → Prop)
    (herr : ∀ᶠ x in 𝓝 τ, P x →
      |v x-D*Singularities.rootRadius c k (x-τ)| ≤
        C*(Singularities.rootRadius c k (x-τ))^2) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ᶠ x in 𝓝 τ, P x →
      lo*|x-τ|^((k:ℝ)⁻¹) ≤ v x ∧ v x ≤ hi*|x-τ|^((k:ℝ)⁻¹) := by
  have hkn : 0 < (k:ℝ) := by exact_mod_cast hk
  have hα : 0 < (k:ℝ)⁻¹ := inv_pos.mpr hkn
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hcscale : 0 < |c|^((k:ℝ)⁻¹) := Real.rpow_pos_of_pos hcpos _
  have hcont : ContinuousAt (fun x : ℝ => Singularities.rootRadius c k (x-τ)) τ := by
    unfold Singularities.rootRadius
    exact ((continuousAt_id.sub_const τ).abs.div_const |c|).rpow_const
      (Or.inr hα.le)
  have hzero : Singularities.rootRadius c k (τ-τ)=0 := by
    simp [Singularities.rootRadius, Real.zero_rpow hα.ne']
  have hsmall : ∀ᶠ x in 𝓝 τ, C*Singularities.rootRadius c k (x-τ) ≤ D/2 := by
    have hlt : C*Singularities.rootRadius c k (τ-τ) < D/2 := by
      rw [hzero,mul_zero]
      exact half_pos hD
    have h := (hcont.const_mul C).eventually (gt_mem_nhds hlt)
    exact h.mono (fun _ hx => hx.le)
  refine ⟨(D/2)/(|c|^((k:ℝ)⁻¹)),(3*D/2)/(|c|^((k:ℝ)⁻¹)),
    div_pos (half_pos hD) hcscale,div_pos (by positivity) hcscale,?_⟩
  filter_upwards [herr,hsmall] with x hx hs hp
  have hh := quadratic_error_comparison
    (Real.rpow_nonneg (div_nonneg (abs_nonneg _) hcpos.le) _) hs (hx hp)
  rw [Real.div_rpow (abs_nonneg (x-τ)) (abs_nonneg c)] at hh
  convert hh using 1 <;> ring

section Profiles
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := ι))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (i : ι)
    (hrep : Represents (fun z => m z i) μ)
    (e : ℝ ≃ᵐ ℝ) (he : (volume : Measure ℝ).map e=volume)
    (hc : Continuous e) (hi : Continuous e.symm)
    (hcenter : e.symm 0 ∉ singularUnion m)
include algebraic puiseux inversion hS hupper heq hμ hrep he hc hi hcenter

theorem cusp_profile_of_comparison (α lo up : ℝ)
    (hcomp : ∀ᶠ x in 𝓝 (0:ℝ),
      lo*|x|^α ≤ realDensity m i (e.symm x) ∧ realDensity m i (e.symm x) ≤ up*|x|^α) :
    ∃ (r : ℝ) (v : ℝ → ℝ), 0 < r ∧ Measurable v ∧ (∀ x, 0 ≤ v x) ∧
      (∀ x ∈ Ioo (-r) r, lo*|x|^α ≤ v x ∧ v x ≤ up*|x|^α) ∧
      (μ.map e).restrict (Ioo (-r) r) =
        (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x)) := by
  have hopen : IsOpen (singularUnion m)ᶜ :=
    (family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
  have hreg : ∀ᶠ x in 𝓝 (0:ℝ), e.symm x ∉ singularUnion m :=
    hi.continuousAt.eventually (hopen.mem_nhds hcenter)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hreg.and hcomp)
  have hb : ∀ x ∈ Ioo (-r) r, e.symm x ∉ singularUnion m ∧
      lo*|x|^α ≤ realDensity m i (e.symm x) ∧ realDensity m i (e.symm x) ≤ up*|x|^α := by
    intro x hx
    apply hball
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hx
  obtain ⟨v,hv,hn,heqv,hmeasure⟩ := actual_transformed_local_density
    algebraic puiseux inversion S a hS m hupper heq μ hμ i hrep e he hc hi
    (Ioo (-r) r) isOpen_Ioo (fun x hx => (hb x hx).1)
  refine ⟨r,v,hr,hv,hn,?_,hmeasure⟩
  intro x hx
  rw [heqv x hx]
  exact (hb x hx).2

theorem edge_profile_of_comparison (α lo up : ℝ)
    (hcomp : ∀ᶠ x in 𝓝 (0:ℝ),
      (0 < x → lo*|x|^α ≤ realDensity m i (e.symm x) ∧
        realDensity m i (e.symm x) ≤ up*|x|^α) ∧
      (x ≤ 0 → realDensity m i (e.symm x)=0)) :
    ∃ (r : ℝ) (v : ℝ → ℝ), 0 < r ∧ Measurable v ∧ (∀ x, 0 ≤ v x) ∧
      (∀ x ∈ Ioo 0 r, lo*|x|^α ≤ v x ∧ v x ≤ up*|x|^α) ∧
      (μ.map e).restrict (Ioo (-r) r) =
        (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x)) := by
  have hopen : IsOpen (singularUnion m)ᶜ :=
    (family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
  have hreg : ∀ᶠ x in 𝓝 (0:ℝ), e.symm x ∉ singularUnion m :=
    hi.continuousAt.eventually (hopen.mem_nhds hcenter)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hreg.and hcomp)
  have hdist : ∀ x ∈ Ioo (-r) r, dist x (0:ℝ)<r := by
    intro x hx
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hx
  obtain ⟨v,hv,hn,heqv,hmeasure⟩ := actual_transformed_local_density
    algebraic puiseux inversion S a hS m hupper heq μ hμ i hrep e he hc hi
    (Ioo (-r) r) isOpen_Ioo (fun x hx => (hball (hdist x hx)).1)
  refine ⟨r,v,hr,hv,hn,?_,hmeasure.trans ?_⟩
  · intro x hx
    have hw : x ∈ Ioo (-r) r := ⟨by linarith [hx.1],hx.2⟩
    rw [heqv x hw]
    exact (hball (hdist x hw)).2.1 hx.1
  · apply edge_half_window v hr
    intro x hx hx0
    rw [heqv x hx]
    exact (hball (hdist x hx)).2.2 hx0

end Profiles

end NonSymmetricDyson.Paper.PoissonMeasureBridge
