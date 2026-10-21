import Dyson.Paper.PoissonMeasureBridge

noncomputable section
open MeasureTheory
open scoped Classical
namespace NonSymmetricDyson.Paper.SingularityPoissonOrientation
open Full Full.Foundations PoissonMeasureBridge

def direction (left : Bool) : ℝ := if left then 1 else -1

def coordinate (τ : ℝ) (left : Bool) : ℝ ≃ᵐ ℝ :=
  if left then translation τ else (translation τ).trans reflection

theorem inverse_coordinate (τ x : ℝ) (left : Bool) :
    (coordinate τ left).symm x=τ+direction left*x := by
  cases left
  · change -x+τ=τ+(-1)*x
    ring
  · change x+τ=τ+1*x
    ring

theorem direction_abs (left : Bool) : |direction left|=1 := by
  cases left <;> norm_num [direction]

theorem coordinate_continuous (τ : ℝ) (left : Bool) : Continuous (coordinate τ left) := by
  cases left
  · change Continuous (fun x:ℝ => -(x-τ))
    fun_prop
  · change Continuous (fun x:ℝ => x-τ)
    fun_prop

theorem inverse_continuous (τ : ℝ) (left : Bool) : Continuous (coordinate τ left).symm := by
  cases left
  · change Continuous (fun x:ℝ => -x+τ)
    fun_prop
  · change Continuous (fun x:ℝ => x+τ)
    fun_prop

theorem coordinate_volume (τ : ℝ) (left : Bool) :
    (volume : Measure ℝ).map (coordinate τ left)=volume := by
  cases left
  · change volume.map (reflection ∘ translation τ)=volume
    rw [← Measure.map_map reflection.measurable (translation τ).measurable,
      translation_volume,reflection_volume]
  · exact translation_volume τ

theorem coordinate_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (τ : ℝ) (left : Bool) : IsProbabilityMeasure (μ.map (coordinate τ left)) :=
  Measure.isProbabilityMeasure_map (coordinate τ left).measurable.aemeasurable

theorem stieltjes_coordinate_im (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℂ → ℂ) (hrep : Represents f μ) (τ E η : ℝ) (hη : 0<η) (left : Bool) :
    (Poisson.stieltjes (μ.map (coordinate τ left)) (Poisson.point E η)).im=
      (f (Poisson.point (τ+direction left*E) η)).im := by
  cases left
  · change (Poisson.stieltjes (μ.map (reflection ∘ translation τ)) (Poisson.point E η)).im=_
    rw [← Measure.map_map reflection.measurable (translation τ).measurable]
    change (Poisson.stieltjes (Poisson.reflectMeasure (Poisson.recenter μ τ)) (Poisson.point E η)).im=_
    letI := Poisson.recenter_probability μ τ
    rw [Poisson.stieltjes_reflect_im _ E hη,Poisson.stieltjes_recenter]
    simpa [direction,Poisson.stieltjes,Poisson.resolvent,add_comm] using
      (congrArg Complex.im (hrep (Poisson.point (τ-E) η) hη)).symm
  · change (Poisson.stieltjes (Poisson.recenter μ τ) (Poisson.point E η)).im=_
    rw [Poisson.stieltjes_recenter]
    simpa [direction,Poisson.stieltjes,Poisson.resolvent,add_comm] using
      (congrArg Complex.im (hrep (Poisson.point (τ+E) η) hη)).symm

end NonSymmetricDyson.Paper.SingularityPoissonOrientation
