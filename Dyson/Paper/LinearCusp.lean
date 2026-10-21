import Dyson.Paper.LinearDensityInverse
import Dyson.Paper.LinearGlobalization
import Dyson.Paper.SingularityPoissonModel
import Dyson.Paper.MeasureRepresentation

/-! The revised M6 cusp conclusion: the actual Poisson lower density scale
and the actual beta-based inverse bound give the requested upper bound only. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearCusp
open Full Full.ExternalAlgebraic
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem cusp_upper_from_density_scale
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (m : ℂ → ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : ι)
    (A : ℝ) (hA : 0 < A)
    (hinverse : ∀ᶠ z in 𝓝[upper] (τ:ℂ), ∀ hz : 0 < z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
        A / (∑ j, (m z j).im)^2)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hscale : ∀ E η : ℝ, 0 < η → |E|+η < ε →
      c*(|E|+η)^((1:ℝ)/3) ≤ (m (Poisson.point (τ+E) η) i).im) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  apply LinearGlobalization.upper_full_height_of_eventual S a m hS hupper heq
    τ ((2:ℝ)/3) (A/c^2) (by norm_num) (by positivity)
  have hq : Tendsto (fun z : ℂ => |z.re-τ|+z.im) (𝓝[upper] (τ:ℂ)) (𝓝 0) := by
    simpa using (show Continuous (fun z : ℂ => |z.re-τ|+z.im) by fun_prop).continuousAt.tendsto.mono_left
      (show 𝓝[upper] (τ:ℂ) ≤ 𝓝 (τ:ℂ) from nhdsWithin_le_nhds)
  filter_upwards [hinverse,hq.eventually_lt_const hε,self_mem_nhdsWithin] with z hzInv hzNear hz
  intro hz'
  have hpoint : Poisson.point (τ+(z.re-τ)) z.im = z := by
    apply Complex.ext <;> simp [Poisson.point]
  have hsc := hscale (z.re-τ) z.im hz hzNear
  rw [hpoint] at hsc
  have hρ : 0 < ∑ j, (m z j).im :=
    Finset.sum_pos (fun j _ => hupper z hz j) Finset.univ_nonempty
  have hiρ : (m z i).im ≤ ∑ j, (m z j).im :=
    Finset.single_le_sum (fun j _ => (hupper z hz j).le) (Finset.mem_univ i)
  have hnorm : ‖z-(τ:ℂ)‖ ≤ |z.re-τ|+z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z-(τ:ℂ))
  have hn : 0 < ‖z-(τ:ℂ)‖ := by
    have hh : z.im ≤ ‖z-(τ:ℂ)‖ := by simpa using Complex.im_le_norm (z-(τ:ℂ))
    exact hz.trans_le hh
  have hp := Real.rpow_le_rpow (norm_nonneg (z-(τ:ℂ))) hnorm
    (by norm_num : (0:ℝ) ≤ 1/3)
  have hlow : c*‖z-(τ:ℂ)‖^((1:ℝ)/3) ≤ ∑ j, (m z j).im :=
    ((mul_le_mul_of_nonneg_left hp hc.le).trans hsc).trans hiρ
  have hpow : (‖z-(τ:ℂ)‖^((1:ℝ)/3))^2 = ‖z-(τ:ℂ)‖^((2:ℝ)/3) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg (z-(τ:ℂ)))]
    norm_num
  have hsq : c^2*‖z-(τ:ℂ)‖^((2:ℝ)/3) ≤ (∑ j, (m z j).im)^2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ c*‖z-(τ:ℂ)‖^((1:ℝ)/3)) hρ.le).mpr hlow
    simpa only [mul_pow,hpow] using hh
  calc
    _ ≤ A/(∑ j, (m z j).im)^2 := hzInv hz'
    _ ≤ A/(c^2*‖z-(τ:ℂ)‖^((2:ℝ)/3)) :=
      div_le_div_of_nonneg_left hA.le (by positivity) hsq
    _ = (A/c^2)/‖z-(τ:ℂ)‖^((2:ℝ)/3) := by rw [div_div]

open Full.Singularities Full.Spectral Full.PerronContinuation

/-- Literal symmetric M6 cusp clause. The local density scale, Perron data,
and inverse bound are constructed from the actual model, then globalized. -/
theorem cusp_symmetric {n : ℕ} (hn : 0 < n)
    (stieltjes : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (hsym : ∀ i j, S i j = S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨μ,hμ⟩ := MeasureRepresentation.upper_solution_probability_representation
    stieltjes S a hS m hupper heq
  obtain ⟨c,C,ε,hc,_,hε,hscale⟩ := SingularityPoissonModel.cusp_symmetric
    perron normalForm orientation hn algebraic puiseux S a hS hirr hsym
    m hupper heq τ i hfront hτ inversion hcusp i (μ i) (hμ i).1 (hμ i).2
  obtain ⟨A,hA,hInv⟩ := LinearFrame.symmetric_density_inverse hn spectral continuousPerron
    algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ
  exact cusp_upper_from_density_scale S a m hS hupper heq τ i A hA hInv
    c ε hc hε (fun E η hη hsmall => (hscale E η hη hsmall).1)

/-- Literal NB M6 cusp clause for a finite model reindexed by its actual
oriented edges and terminal potential. No cusp lower inverse bound is exported. -/
theorem cusp_nonbacktracking {n : ℕ} (hn : 0 < n)
    (stieltjes : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀ i j, S i j = G.matrix (e i) (e j))
    (hpot : ∀ i, a i = av (G.head (e i)))
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (z : ℂ) (hz : 0 < z.im), |z.re-τ| ≤ δ →
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
          C * max 1 (1/(|z.re-τ|+z.im)^((2:ℝ)/3)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨μ,hμ⟩ := MeasureRepresentation.upper_solution_probability_representation
    stieltjes S a hS m hupper heq
  obtain ⟨c,C,ε,hc,_,hε,hscale⟩ := SingularityPoissonModel.cusp_nonbacktracking
    perron normalForm orientation hn algebraic puiseux S a hS hirr G deg e av hmat hpot
    m hupper heq τ i hfront hτ inversion hcusp i (μ i) (hμ i).1 (hμ i).2
  obtain ⟨A,hA,hInv⟩ := LinearFrame.nonbacktracking_density_inverse hn spectral continuousPerron
    algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ
  exact cusp_upper_from_density_scale S a m hS hupper heq τ i A hA hInv
    c ε hc hε (fun E η hη hsmall => (hscale E η hη hsmall).1)

end NonSymmetricDyson.Paper.LinearCusp
