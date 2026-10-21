import Dyson.Paper.Singularities
import Dyson.Paper.PoissonMeasureBridge
import Dyson.Paper.SingularityPoissonOrientation

/-! Actual M5 asymptotics produce local probability-measure density profiles;
Poisson integration then gives the imaginary-part scales used in M6. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace NonSymmetricDyson.Paper.SingularityPoissonProfiles
open Full Full.Singularities Foundations Boundary BoundaryMeasure PoissonMeasureBridge
variable {ι : Type*} [Fintype ι]

/-- Local cusp profile extracted from an asymptotic law; final model theorems
below supply that law from M5 rather than assuming a density profile. -/
theorem cusp_profile_from_asymptotic
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=ι))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory) (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j,0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (j : ι)
    (hrep : Represents (fun z => m z j) μ) (τ : ℝ) (hτ : τ∉singularUnion m)
    (c D C : ℝ) (hc : c≠0) (hD : 0<D)
    (herr : ∀ᶠ x in 𝓝 τ,
      |realDensity m j x-D*rootRadius c 3 (x-τ)| ≤ C*(rootRadius c 3 (x-τ))^2) :
    ∃ lo up r : ℝ,∃ v : ℝ → ℝ,0<lo ∧ 0<up ∧ 0<r ∧ Measurable v ∧
      (∀ x,0 ≤ v x) ∧
      (∀ x∈Ioo (-r) r,lo*|x|^((1:ℝ)/3) ≤ v x ∧ v x ≤ up*|x|^((1:ℝ)/3)) ∧
      (Poisson.recenter μ τ).restrict (Ioo (-r) r)=
        (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x)) := by
  obtain ⟨lo,up,hlo,hup,hcomp⟩ := root_asymptotic_comparison
    (realDensity m j) τ c D C 3 hc hD (by norm_num) (fun _ => True)
    (herr.mono fun _ hh _ => hh)
  have ht : Tendsto (fun x:ℝ => x+τ) (𝓝 0) (𝓝 τ) := by
    simpa using (by fun_prop : Continuous (fun x:ℝ => x+τ)).tendsto (0:ℝ)
  have hcomp' : ∀ᶠ x in 𝓝 (0:ℝ),
      lo*|x|^((1:ℝ)/3) ≤ realDensity m j ((translation τ).symm x) ∧
      realDensity m j ((translation τ).symm x) ≤ up*|x|^((1:ℝ)/3) := by
    filter_upwards [ht.eventually hcomp] with x hx
    simpa [translation] using hx trivial
  obtain ⟨r,v,hr,hv,hn,hbounds,hmeasure⟩ := cusp_profile_of_comparison
    algebraic puiseux inversion S a hS m hupper heq μ hμ j hrep
    (translation τ) (translation_volume τ)
    (by change Continuous (fun x:ℝ => x-τ);fun_prop)
    (by change Continuous (fun x:ℝ => x+τ);fun_prop)
    (by simpa [translation] using hτ) ((1:ℝ)/3) lo up hcomp'
  exact ⟨lo,up,r,v,hlo,hup,hr,hv,hn,hbounds,hmeasure⟩

/-- Exact passage from the actual local profile to the original solution's
imaginary part. All remote mass, including atoms, stays in μ. -/
theorem cusp_imaginary_from_profile
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (f : ℂ → ℂ)
    (hrep : Represents f μ) (τ lo up r : ℝ) (v : ℝ → ℝ)
    (hlo : 0<lo) (hup : 0<up) (hr : 0<r) (hv : Measurable v)
    (hn : ∀ x,0 ≤ v x)
    (hcomp : ∀ x∈Ioo (-r) r,lo*|x|^((1:ℝ)/3) ≤ v x ∧ v x ≤ up*|x|^((1:ℝ)/3))
    (hmeas : (Poisson.recenter μ τ).restrict (Ioo (-r) r)=
      (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    ∃ c C ε : ℝ,0<c ∧ 0<C ∧ 0<ε ∧ ∀ E η : ℝ,0<η → |E|+η<ε →
      c*(|E|+η)^((1:ℝ)/3) ≤ (f (Poisson.point (τ+E) η)).im ∧
      (f (Poisson.point (τ+E) η)).im ≤ C*(|E|+η)^((1:ℝ)/3) := by
  letI := hμ
  letI := Poisson.recenter_probability μ τ
  let B : ℝ := up*(Real.pi+Poisson.fractionalMoment ((1:ℝ)/3))+4/r^2
  refine ⟨lo/5,|B|+1,min (r/8) 1,by positivity,by positivity,
    lt_min (by positivity) (by norm_num),?_⟩
  intro E η hη hsmall
  have hh := Poisson.cusp_measure_scale (Poisson.recenter μ τ)
    (by norm_num : 0<(1:ℝ)/3) (by norm_num : (1:ℝ)/3<1) hlo.le hup.le hr hη
    (hsmall.trans_le (min_le_left _ _)) (hsmall.le.trans (min_le_right _ _)) hv hn
    (fun x hx => (hcomp x hx).1) (fun x hx => (hcomp x hx).2) hmeas
  have he : (Poisson.stieltjes (Poisson.recenter μ τ) (Poisson.point E η)).im=
      (f (Poisson.point (τ+E) η)).im := by
    rw [Poisson.stieltjes_recenter]
    rw [hrep _ hη]
    simp [Poisson.stieltjes,Poisson.resolvent,add_comm]
  rw [he] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · exact (le_abs_self B).trans (by linarith [abs_nonneg B])
  · positivity

open SingularityPoissonOrientation

/-- Both possible edge orientations, obtained from the physical one-sided
asymptotic and the exact vanishing of the gap density. -/
theorem edge_profile_from_asymptotic
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=ι))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory) (inversion : ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j,0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (j : ι)
    (hrep : Represents (fun z => m z j) μ) (τ : ℝ) (hτ : τ∉singularUnion m)
    (hzero : realDensity m j τ=0) (c D C : ℝ) (hc : c≠0) (hD : 0<D)
    (left : Bool) (hdir : c*direction left<0)
    (herr : ∀ᶠ x in 𝓝 τ,
      (c*(x-τ)<0 → |realDensity m j x-D*rootRadius c 2 (x-τ)| ≤ C*(rootRadius c 2 (x-τ))^2) ∧
      (0<c*(x-τ) → realDensity m j x=0)) :
    ∃ (lo up r : ℝ) (v : ℝ → ℝ),0<lo ∧ 0<up ∧ 0<r ∧ Measurable v ∧
      (∀ x,0 ≤ v x) ∧
      (∀ x∈Ioo 0 r,lo*|x|^((1:ℝ)/2) ≤ v x ∧ v x ≤ up*|x|^((1:ℝ)/2)) ∧
      (μ.map (coordinate τ left)).restrict (Ioo (-r) r)=
        (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x)) := by
  obtain ⟨lo,up,hlo,hup,hcomp⟩ := root_asymptotic_comparison
    (realDensity m j) τ c D C 2 hc hD (by norm_num) (fun x => c*(x-τ)<0)
    (herr.mono fun _ hx => hx.1)
  have ht : Tendsto (coordinate τ left).symm (𝓝 0) (𝓝 τ) := by
    simpa [inverse_coordinate] using (inverse_continuous τ left).tendsto (0:ℝ)
  have hcomp' : ∀ᶠ x in 𝓝 (0:ℝ),
      (0<x → lo*|x|^((1:ℝ)/2) ≤ realDensity m j ((coordinate τ left).symm x) ∧
        realDensity m j ((coordinate τ left).symm x) ≤ up*|x|^((1:ℝ)/2)) ∧
      (x≤0 → realDensity m j ((coordinate τ left).symm x)=0) := by
    filter_upwards [ht.eventually hcomp,ht.eventually herr] with x hx herrx
    have habs : |(coordinate τ left).symm x-τ|=|x| := by
      rw [inverse_coordinate,add_sub_cancel_left,abs_mul,direction_abs,one_mul]
    constructor
    · intro hp
      have hh : c*((coordinate τ left).symm x-τ)<0 := by
        rw [inverse_coordinate,add_sub_cancel_left]
        nlinarith [mul_neg_of_neg_of_pos hdir hp]
      simpa only [habs,Nat.cast_ofNat,inv_eq_one_div] using hx hh
    · intro hn
      by_cases hz : x=0
      · simpa [hz,inverse_coordinate] using hzero
      · have hneg : x<0 := lt_of_le_of_ne hn hz
        apply herrx.2
        rw [inverse_coordinate,add_sub_cancel_left]
        nlinarith [mul_pos_of_neg_of_neg hdir hneg]
  obtain ⟨r,v,hr,hv,hn,hbounds,hmeasure⟩ := edge_profile_of_comparison
    algebraic puiseux inversion S a hS m hupper heq μ hμ j hrep
    (coordinate τ left) (coordinate_volume τ left)
    (coordinate_continuous τ left) (inverse_continuous τ left)
    (by simpa [inverse_coordinate] using hτ) ((1:ℝ)/2) lo up hcomp'
  exact ⟨lo,up,r,v,hlo,hup,hr,hv,hn,hbounds,hmeasure⟩

/-- The two original edge Poisson scales, for the actual physical component
on the support and gap sides in either orientation. -/
theorem edge_imaginary_from_profile
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (f : ℂ → ℂ)
    (hrep : Represents f μ) (τ : ℝ) (left : Bool) (lo up r : ℝ) (v : ℝ → ℝ)
    (hlo : 0<lo) (hup : 0<up) (hr : 0<r) (hv : Measurable v)
    (hn : ∀ x,0 ≤ v x)
    (hcomp : ∀ x∈Ioo 0 r,lo*|x|^((1:ℝ)/2) ≤ v x ∧ v x ≤ up*|x|^((1:ℝ)/2))
    (hmeas : (μ.map (coordinate τ left)).restrict (Ioo (-r) r)=
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    ∃ cs Cs cg Cg ε : ℝ,0<cs ∧ 0<Cs ∧ 0<cg ∧ 0<Cg ∧ 0<ε ∧
      ∀ κ η : ℝ,0≤κ → 0<η → κ+η<ε →
        (cs*Real.sqrt (κ+η) ≤ (f (Poisson.point (τ+direction left*κ) η)).im ∧
          (f (Poisson.point (τ+direction left*κ) η)).im ≤ Cs*Real.sqrt (κ+η)) ∧
        (cg*(η/Real.sqrt (κ+η)) ≤ (f (Poisson.point (τ-direction left*κ) η)).im ∧
          (f (Poisson.point (τ-direction left*κ) η)).im ≤ Cg*(η/Real.sqrt (κ+η))) := by
  letI := hμ
  letI := coordinate_probability μ τ left
  let Bs : ℝ := up*(Real.pi+Poisson.fractionalMoment ((1:ℝ)/2))+4/r^2
  let Bg : ℝ := 2*up*Poisson.gapMoment ((1:ℝ)/2)+4/r^2
  refine ⟨lo/5,|Bs|+1,lo/10,|Bg|+1,min (r/8) 1,
    by positivity,by positivity,by positivity,by positivity,
    lt_min (by positivity) (by norm_num),?_⟩
  intro κ η hκ hη hs
  have hsmall := hs.trans_le (min_le_left (r/8) 1)
  have hq1 := hs.le.trans (min_le_right (r/8) 1)
  have hsupport := Poisson.edge_support_measure_scale (μ.map (coordinate τ left))
    (by norm_num : 0<(1:ℝ)/2) (by norm_num : (1:ℝ)/2<1) hlo.le hup.le hr hκ hη
    hsmall hq1 hv hn (fun x hx => (hcomp x hx).1) (fun x hx => (hcomp x hx).2) hmeas
  have hgap := Poisson.edge_gap_measure_scale (μ.map (coordinate τ left))
    (by norm_num : 0<(1:ℝ)/2) (by norm_num : (1:ℝ)/2<1) hlo.le hup.le hr hκ hη
    hsmall hq1 hv hn (fun x hx => (hcomp x hx).1) (fun x hx => (hcomp x hx).2) hmeas
  rw [← Real.sqrt_eq_rpow,stieltjes_coordinate_im μ f hrep τ κ η hη left] at hsupport
  rw [Poisson.half_gap_scale,stieltjes_coordinate_im μ f hrep τ (-κ) η hη left] at hgap
  have he : τ+direction left*(-κ)=τ-direction left*κ := by ring
  rw [he] at hgap
  constructor
  · exact ⟨hsupport.1,hsupport.2.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self Bs).trans (by linarith [abs_nonneg Bs])) (Real.sqrt_nonneg _))⟩
  · exact ⟨hgap.1,hgap.2.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self Bg).trans (by linarith [abs_nonneg Bg])) (by positivity))⟩

end NonSymmetricDyson.Paper.SingularityPoissonProfiles
