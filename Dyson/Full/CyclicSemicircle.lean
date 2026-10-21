import Dyson.Full.CyclicGeneralInverse
import Dyson.Full.MainBoundary

/-! Global semicircle law for every directed cycle: actual upper-half-plane
solution, boundedness, absence of singular points, exact density and no atoms. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set MeasureTheory

namespace NonSymmetricDyson.Full.CyclicGeneral

open CyclicExample (scalar root)

/-- The chosen explicit square-root branch has positive imaginary solution
throughout the upper half-plane, not only near the resonant energy. -/
theorem scalar_upper {z : ℂ} (hz : 0<z.im) : 0<(scalar z).im := by
  let t : ℂ := 4-z^2
  have hre : t.re=4-z.re^2+z.im^2 := by simp [t, pow_two, Complex.mul_re]; ring
  have him : t.im= -2*z.re*z.im := by simp [t, pow_two, Complex.mul_im]; ring
  have hn : ‖t‖^2=(4-z.re^2+z.im^2)^2+(-2*z.re*z.im)^2 := by
    simpa [Complex.normSq_apply, hre, him, pow_two] using (Complex.normSq_eq_norm_sq t).symm
  have hdiff : ‖t‖^2-(z.re^2+z.im^2-4)^2=16*z.im^2 := by nlinarith [hn]
  have hgt : z.re^2+z.im^2-4 < ‖t‖ := by
    by_contra hh
    have hle := le_of_not_gt hh
    have hp : 0 ≤ z.re^2+z.im^2-4 := (norm_nonneg t).trans hle
    have hs := sq_le_sq₀ (norm_nonneg t) hp |>.mpr hle
    nlinarith [sq_pos_of_pos hz]
  have hnonneg : 0 ≤ (‖t‖+t.re)/2 := by
    have hr := (abs_le.mp (Complex.abs_re_le_norm t)).1
    linarith
  have hsqrt := Real.sq_sqrt hnonneg
  have hr : (root z).re=Real.sqrt ((‖t‖+t.re)/2) := Complex.cpow_inv_two_re t
  have hroot : z.im < (root z).re := by
    rw [hr, hre]
    rw [hre] at hsqrt
    nlinarith [Real.sqrt_nonneg ((‖t‖+(4-z.re^2+z.im^2))/2)]
  have he : (scalar z).im=((root z).re-z.im)/2 := by simp [scalar]; ring
  rw [he]
  exact div_pos (sub_pos.mpr hroot) (by norm_num)

variable (d : ℕ) [NeZero d]

theorem canonical_eq_scalar_global {z : ℂ} (hz : 0<z.im) :
    GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d) z =
      fun _ => scalar z := canonical_eq_scalar d hz (scalar_upper hz)

theorem canonical_uniform_bound {z : ℂ} (hz : 0<z.im) (i : Fin d) :
    ‖GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d) z i‖<1 := by
  rw [canonical_eq_scalar_global d hz]
  exact scalar_norm_lt_one d hz (scalar_upper hz)

def canonical : ℂ → Fin d → ℂ :=
  GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d)

theorem canonical_upper (z : ℂ) (hz : z ∈ ExternalAlgebraic.upper) :
    BasicEstimates.IsUpperSolution (canonical d z) :=
  GlobalWellPosedness.solution_upper (fun _ => 0) (cycle_nonnegative d) hz

theorem canonical_equation (z : ℂ) (hz : z ∈ ExternalAlgebraic.upper) :
    BasicEstimates.IsDysonSolution (cycle d) (fun _ => 0) z (canonical d z) :=
  GlobalWellPosedness.solution_equation (fun _ => 0) (cycle_nonnegative d) hz

theorem singularSet_empty (i : Fin d) :
    Boundary.singularSet (fun z => canonical d z i)=∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro τ
  apply Boundary.not_singular_of_bounded (M := 1)
  intro η hη
  exact (canonical_uniform_bound d (by simpa [Boundary.vertical] using hη) i).le

theorem singularUnion_empty : Boundary.singularUnion (canonical d)=∅ := by
  simp [Boundary.singularUnion, singularSet_empty]

/-- Every upper or real limit of the scalar quadratic has the semicircle
imaginary part.  This includes the endpoints and the exterior real axis. -/
theorem quadratic_imaginary (τ : ℝ) (b : ℂ) (hi : 0≤b.im)
    (he : b^2+(τ : ℂ)*b+1=0) : b.im=Real.sqrt (4-τ^2)/2 := by
  have hr := congrArg Complex.re he
  have hm := congrArg Complex.im he
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.zero_re, zero_mul, sub_zero] at hr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_im, Complex.zero_im, zero_mul, add_zero] at hm
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hr hm
  by_cases hb : b.im=0
  · have hrad : 4-τ^2≤0 := by rw [hb] at hr; nlinarith [sq_nonneg (2*b.re+τ)]
    rw [Real.sqrt_eq_zero_of_nonpos hrad, hb]
    norm_num
  · have hbpos := lt_of_le_of_ne hi (Ne.symm hb)
    have hx : 2*b.re+τ=0 := by
      have hh : b.im*(2*b.re+τ)=0 := by nlinarith [hm]
      exact (mul_eq_zero.mp hh).resolve_left hb
    have hsq : (2*b.im)^2=4-τ^2 := by nlinarith [hr]
    rw [← hsq, Real.sqrt_sq (by positivity)]
    ring

variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin d))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)

include algebraic puiseux in
theorem canonical_boundary_limits (τ : ℝ) :
    Boundary.IsBoundaryValue (canonical d) τ
      (Boundary.boundaryVector (canonical d) (τ : ℂ)) := by
  apply Boundary.family_boundary_limits algebraic puiseux (cycle d) (fun _ => 0)
    (cycle_nonnegative d) (canonical d) (canonical_upper d) (canonical_equation d) τ
  simp [singularUnion_empty]

include algebraic puiseux in
theorem canonical_boundary_imaginary (τ : ℝ) (i : Fin d) :
    (Boundary.boundaryVector (canonical d) (τ : ℂ) i).im=Real.sqrt (4-τ^2)/2 := by
  let b := Boundary.boundaryVector (canonical d) (τ : ℂ) i
  have hlim := tendsto_pi_nhds.mp (canonical_boundary_limits d algebraic puiseux τ) i
  have hnonneg := (Boundary.family_boundary_equation algebraic puiseux (cycle d)
    (fun _ => 0) (cycle_nonnegative d) (canonical d) (canonical_upper d)
    (canonical_equation d) τ (by simp [singularUnion_empty])).2.1 i
  apply quadratic_imaginary τ b hnonneg
  have hp := ((hlim.pow 2).add ((Boundary.vertical_tendsto τ).mul hlim)).add_const (1 : ℂ)
  have hzero : Tendsto (fun η : ℝ => (canonical d (Boundary.vertical τ η) i)^2+
      Boundary.vertical τ η*canonical d (Boundary.vertical τ η) i+1)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hz : 0 < (Boundary.vertical τ η).im := by simpa [Boundary.vertical] using hη
    change 0 = (GlobalWellPosedness.solution (cycle d) (fun _ => 0)
      (cycle_nonnegative d) (Boundary.vertical τ η) i)^2+_+1
    simp only [canonical, canonical_eq_scalar_global d hz]
    exact (CyclicExample.scalar_quadratic _).symm
  exact tendsto_nhds_unique hp hzero

include algebraic puiseux in
theorem regularSupport_eq (i : Fin d) :
    Boundary.regularSupport (canonical d) i=Set.Ioo (-2) 2 := by
  ext τ
  simp only [Boundary.regularSupport, Set.mem_setOf_eq, singularUnion_empty,
    Set.mem_empty_iff_false, not_false_eq_true, true_and, Set.mem_Ioo,
    canonical_boundary_imaginary d algebraic puiseux]
  rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℝ)<2), Real.sqrt_pos]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (τ+2), sq_nonneg (τ-2)]
  · rintro ⟨hlo,hhi⟩
    nlinarith

/-- The density is written with the usual convention `sqrt x=0` for `x≤0`. -/
def semicircle : Measure ℝ := volume.withDensity
  (fun τ => ENNReal.ofReal (Real.sqrt (4-τ^2)/(2*Real.pi)))

instance semicircle_noAtoms : NoAtoms semicircle := by unfold semicircle; infer_instance

include algebraic puiseux in
theorem represented_measure_eq_semicircle (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (μ : Measure ℝ) (hμ : IsProbabilityMeasure μ) (i : Fin d)
    (hrep : Foundations.Represents (fun z => canonical d z i) μ) : μ=semicircle := by
  have ha := Boundary.family_coordinate_analytic (cycle d) (fun _ => 0)
    (cycle_nonnegative d) (canonical d) (canonical_upper d) (canonical_equation d) i
  have halg := ExternalAlgebraic.solution_algebraic algebraic (cycle d) (fun _ => 0)
    (cycle_nonnegative d) (canonical d) (canonical_upper d) (canonical_equation d) i
  have hc := Boundary.algebraic_continuous_extension puiseux (fun z => canonical d z i)
    ha halg (fun z hz => canonical_upper d z hz i)
  have hm : μ=BoundaryMeasure.densityMeasure (fun z => Boundary.boundaryVector (canonical d) z i) := by
    have hh := BoundaryMeasure.finite_exceptional_decomposition inversion μ
      (fun z => canonical d z i) (fun z => Boundary.boundaryVector (canonical d) z i)
      ∅ hμ hrep
      (by simpa [BoundaryMeasure.boundaryDomain, Boundary.regularDomain,
        singularSet_empty, Boundary.boundaryVector] using hc.1) hc.2.1
    simpa using hh
  rw [hm]
  unfold BoundaryMeasure.densityMeasure semicircle
  congr 1
  funext τ
  unfold BoundaryMeasure.boundaryDensity
  dsimp only
  rw [canonical_boundary_imaginary d algebraic puiseux]
  congr 1
  ring

include algebraic puiseux in
/-- Complete semicircle identification for the actual canonical cycle solution,
using only the already isolated general Stieltjes and algebraic-function inputs. -/
theorem canonical_semicircle_measure (ext : Foundations.ExternalStieltjesTheory (Fin d))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion) :
    IsProbabilityMeasure semicircle ∧
    (∀ i : Fin d, Foundations.Represents (fun z => canonical d z i) semicircle) ∧
    NoAtoms semicircle := by
  obtain ⟨μ,hμ⟩ := Foundations.canonical_probability_representation ext (fun _ => 0)
    (cycle_nonnegative d)
  have he (i : Fin d) : μ i=semicircle :=
    represented_measure_eq_semicircle d algebraic puiseux inversion (μ i) (hμ i).1 i (hμ i).2
  refine ⟨?_, ?_, inferInstance⟩
  · rw [← he 0]
    exact (hμ 0).1
  · intro i
    rw [← he i]
    exact (hμ i).2

end NonSymmetricDyson.Full.CyclicGeneral
