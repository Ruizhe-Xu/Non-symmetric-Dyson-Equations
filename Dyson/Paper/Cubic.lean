import Dyson.Paper.SingularitiesFrontierNB
import Dyson.Full.MainSingularCubic
import Dyson.Full.SingularitiesHolder

/-! The literal scalar coordinate and cubic error inequalities, including
its imaginary error and full closed-neighborhood two-point 1/3-Hölder clause.
The exact finite-vector reduction and coefficient computations are internal;
the scalar analytic normal-form/vanishing-order principles are explicit. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Cubic
open Full Full.Singularities SingularitiesFrontier

theorem equation_with_perron_data
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m)
    (D : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) :
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  exact frontier_data_cubic_error normalForm imaginaryOrder hn algebraic puiseux S a hS m hupper heq τ hτ D


theorem equation_symmetric
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  obtain ⟨D⟩ := symmetric_frontier_data perron hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ
  exact ⟨D, equation_with_perron_data normalForm imaginaryOrder hn algebraic puiseux S a hS m hupper heq τ hτ D⟩


theorem equation_nonbacktracking
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀ i j,S i j=G.matrix (e i) (e j))
    (hpot : ∀ i,a i=av (G.head (e i)))
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  obtain ⟨D⟩ := nb_frontier_data perron hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ
  exact ⟨D, equation_with_perron_data normalForm imaginaryOrder hn algebraic puiseux S a hS m hupper heq τ hτ D⟩


theorem holder_with_perron_data
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (D : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ z ∈ ExternalAlgebraic.closedUpper, ∀ w ∈ ExternalAlgebraic.closedUpper,
        ‖z-(τ : ℂ)‖ < ε → ‖w-(τ : ℂ)‖ < ε →
        ‖Boundary.boundaryVector m z-Boundary.boundaryVector m w‖ ≤ C * ‖z-w‖ ^ ((1 : ℝ)/3) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨P,_,_⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ D
  obtain ⟨C, r, hC, hr, hholder⟩ := P.upper_one_third_holder
  obtain ⟨_, hregular⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨r₀, hr₀, hreal⟩ := Metric.mem_nhds_iff.mp hregular
  let ε : ℝ := min r r₀
  have hε : 0 < ε := lt_min hr hr₀
  have hdomain (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) (hzε : ‖z-(τ : ℂ)‖<ε) :
      z ∈ Boundary.commonRegularDomain m := by
    by_cases hzi : 0 < z.im
    · exact Or.inl hzi
    · have hzero : z.im = 0 := le_antisymm (le_of_not_gt hzi) hz
      have hzreal : (z.re : ℂ)=z := Complex.ext rfl (by simpa using hzero.symm)
      have hdist : dist z.re τ < r₀ := by
        have hh := Complex.abs_re_le_norm (z-(τ : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at hh
        simpa only [Real.dist_eq] using hh.trans_lt (hzε.trans_le (min_le_right _ _))
      exact Or.inr ⟨z.re, (hreal hdist).1, hzreal⟩
  let lift : ℂ → ℝ → ℂ := fun z η => z+(η : ℂ)*Complex.I
  have hliftlim (z : ℂ) : Tendsto (lift z) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous (lift z) := by dsimp [lift]; fun_prop
    simpa [lift] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hliftup (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) {η : ℝ} (hη : 0<η) :
      lift z η ∈ ExternalAlgebraic.upper := by
    change 0 < (lift z η).im
    simpa [lift] using add_pos_of_nonneg_of_pos hz hη
  have hlim (z : ℂ) (hz : z ∈ ExternalAlgebraic.closedUpper) (hzε : ‖z-(τ : ℂ)‖<ε) :
      Tendsto (fun η => Boundary.boundaryVector m (lift z η)) (𝓝[>] (0 : ℝ))
        (𝓝 (Boundary.boundaryVector m z)) := by
    have hb := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      z (hdomain z hz hzε)
    apply hb.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hliftlim z, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact Or.inl (hliftup z hz hη)
  refine ⟨C, ε, hC, hε, ?_⟩
  intro z hz w hw hzε hwε
  apply le_of_tendsto ((hlim z hz hzε).sub (hlim w hw hwε)).norm
  have hznear : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖lift z η-(τ : ℂ)‖<r := by
    exact ((hliftlim z).sub_const (τ : ℂ)).norm.eventually_lt_const
      (hzε.trans_le (min_le_left _ _))
  have hwnear : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖lift w η-(τ : ℂ)‖<r := by
    exact ((hliftlim w).sub_const (τ : ℂ)).norm.eventually_lt_const
      (hwε.trans_le (min_le_left _ _))
  filter_upwards [self_mem_nhdsWithin, hznear, hwnear] with η hη hzη hwη
  have hzu := hliftup z hz hη
  have hwu := hliftup w hw hη
  rw [Boundary.family_extension_agrees S a hS m hupper heq (lift z η) hzu,
    Boundary.family_extension_agrees S a hS m hupper heq (lift w η) hwu]
  have hh := hholder (lift z η) hzu (lift w η) hwu hzη hwη
  have he : lift z η-lift w η=z-w := by dsimp [lift]; ring
  simpa only [he] using hh

end NonSymmetricDyson.Paper.Cubic
