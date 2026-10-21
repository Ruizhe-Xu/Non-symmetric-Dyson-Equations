import Mathlib
import Dyson.LocalSolvability
import Dyson.PolynomialDyson
import Dyson.Full.Poisson
import Dyson.Full.Linear

/-! Differentiating the actual boundary equation. The identity on the upper
half-plane is enough: neither an equation at real energies nor an analytic
continuation of that equation is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace NonSymmetricDyson.Full.OffSupport

/-- A holomorphic first-order germ that vanishes on the vertical upper ray
has both zero value and zero derivative at the endpoint. -/
theorem upper_ray_vanishing_derivative (f : ℂ → ℂ) (d : ℂ) (E : ℝ)
    (hder : HasDerivAt f d (E : ℂ))
    (hzero : ∀ η : ℝ, 0 < η → f ((E : ℂ) + (η : ℂ) * Complex.I) = 0) :
    f (E : ℂ) = 0 ∧ d = 0 := by
  let path : ℝ → ℂ := fun η => (E : ℂ) + (η : ℂ) * Complex.I
  have hp : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (E : ℂ)) := by
    have ht : ContinuousAt path 0 := by dsimp [path]; fun_prop
    simpa only [path, Complex.ofReal_zero, zero_mul, add_zero] using
      ht.tendsto.mono_left nhdsWithin_le_nhds
  have hz : (fun η => f (path η)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hzero η hη
  have hvalue : f (E : ℂ) = 0 := tendsto_nhds_unique
    (hder.continuousAt.tendsto.comp hp) (tendsto_const_nhds.congr' hz.symm)
  have hpne : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝[≠] (E : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hp, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    change path η ≠ (E : ℂ)
    intro heq
    have hi := congrArg Complex.im heq
    simp only [path, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add] at hi
    exact (ne_of_gt hη) hi
  have hs := (hasDerivAt_iff_tendsto_slope.mp hder).comp hpne
  have hs0 : (fun η => slope f (E : ℂ) (path η)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [hz] with η hη
    simp [slope, hη, hvalue]
  exact ⟨hvalue, tendsto_nhds_unique hs (tendsto_const_nhds.congr' hs0.symm)⟩

variable {ι : Type*} [Fintype ι]

/-- The off-support derivative identity `L m' = m²` follows from the
actual Dyson equations and actual coordinate derivatives. -/
theorem dyson_boundary_derivative
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (E : ℝ)
    (m : ℂ → ι → ℂ) (w : ι → ℂ)
    (hder : ∀ i, HasDerivAt (fun z => m z i) (w i) (E : ℂ))
    (hsol : ∀ η : ℝ, 0 < η → BasicEstimates.IsDysonSolution S a
      ((E : ℂ) + (η : ℂ) * Complex.I) (m ((E : ℂ) + (η : ℂ) * Complex.I)))
    (hne : ∀ η : ℝ, 0 < η → ∀ i, m ((E : ℂ) + (η : ℂ) * Complex.I) i ≠ 0) :
    PolynomialDyson.IsPolynomialSolution S a (E : ℂ) (m (E : ℂ)) ∧
      InteriorStability.stabilityOperator S (m (E : ℂ)) w = fun i => m (E : ℂ) i ^ 2 := by
  have hdata : ∀ i,
      1 + m (E : ℂ) i * ((E : ℂ) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (E : ℂ) j) = 0 ∧
      w i * ((E : ℂ) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (E : ℂ) j) +
        m (E : ℂ) i * (1 + ∑ j, (S i j : ℂ) * w j) = 0 := by
    intro i
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hder j).const_mul (S i j : ℂ))
    have hd := (((hasDerivAt_id (E : ℂ)).sub_const (a i : ℂ)).add hs)
    have hf := ((hder i).mul hd).const_add 1
    apply upper_ray_vanishing_derivative _ _ E hf
    intro η hη
    have hp := PolynomialDyson.of_dyson (hsol η hη) (hne η hη) i
    dsimp only [Pi.mul_apply, Pi.add_apply, id_eq]
    linear_combination -hp
  constructor
  · intro i
    have hp := (hdata i).1
    linear_combination -hp
  · ext i
    simp only [InteriorStability.stabilityOperator_apply]
    have hp := (hdata i).1
    have hd := (hdata i).2
    linear_combination (w i) * hp - (m (E : ℂ) i) * hd

def realStieltjes (μ : Measure ℝ) (E : ℝ) : ℝ := ∫ t, (t - E)⁻¹ ∂μ

theorem stieltjes_real (μ : Measure ℝ) (E : ℝ) :
    Poisson.stieltjes μ (Poisson.point E 0) = (realStieltjes μ E : ℂ) := by
  rw [Poisson.stieltjes, realStieltjes, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with t
  change ((t : ℂ) - (E : ℂ))⁻¹ = (((t-E)⁻¹ : ℝ) : ℂ)
  norm_cast

theorem measure_boundary_dyson_data
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (E ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ i, ∀ᵐ t ∂μ i, ε ≤ |t-E|)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) :
    BasicEstimates.IsDysonSolution S a (E : ℂ)
      (fun i => (realStieltjes (μ i) E : ℂ)) ∧
    (∀ i, realStieltjes (μ i) E ≠ 0) ∧
    (∀ i, Poisson.weight (μ i) E - (realStieltjes (μ i) E)^2 *
      ∑ j, S i j * Poisson.weight (μ j) E = (realStieltjes (μ i) E)^2) := by
  letI : ∀ i, IsProbabilityMeasure (μ i) := hμ
  have hd := dyson_boundary_derivative S a E
    (fun z i => Poisson.stieltjes (μ i) z) (fun i => (Poisson.weight (μ i) E : ℂ))
    (fun i => Poisson.hasDerivAt_stieltjes (μ i) hε (hgap i))
    (fun η hη => hsol _ (by simpa))
    (fun η hη => BasicEstimates.component_ne_zero (hupper _ (by simpa)))
  have heq (i : ι) : Poisson.stieltjes (μ i) (E : ℂ) =
      (realStieltjes (μ i) E : ℂ) := stieltjes_real (μ i) E
  dsimp only at hd
  simp only [heq] at hd
  refine ⟨PolynomialDyson.to_dyson hd.1, ?_, ?_⟩
  · intro i hi
    exact PolynomialDyson.component_ne_zero hd.1 i (by simp [hi])
  · intro i
    have hh := congrArg (fun v : ι → ℂ => (v i).re) hd.2
    simpa [InteriorStability.stabilityOperator_apply, ← Complex.ofReal_pow] using hh

/-- A real-axis coercivity estimate from actual probability measures and
Dyson identities. The only geometric hypotheses are the two support bounds. -/
theorem real_axis_measure_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hS : ∀ i j, 0 ≤ S i j) (E ε D b : ℝ)
    (hε : 0 < ε) (hD : 0 < D) (hb : 0 < b)
    (hgap : ∀ i, ∀ᵐ t ∂μ i, ε ≤ |t-E|)
    (hfar : ∀ i, ∀ᵐ t ∂μ i, |t-E| ≤ D)
    (hmod : ∀ i, b ≤ |realStieltjes (μ i) E|)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) (u : ι → ℂ) :
    ‖u‖ ≤ ((ε⁻¹)^2 / ((D⁻¹)^2 * (b^2 * ε^2))) *
      ‖InteriorStability.stabilityOperator S
        (fun i => Poisson.stieltjes (μ i) (Poisson.point E 0)) u‖ := by
  letI : ∀ i, IsProbabilityMeasure (μ i) := hμ
  have hd := measure_boundary_dyson_data S a μ hμ E ε hε hgap hupper hsol
  have hw i := Poisson.weight_bounds (μ i) hε hD (hgap i) (hfar i)
  have hc : ∀ i, (b ^ 2 * ε ^ 2) * Poisson.weight (μ i) E ≤
      realStieltjes (μ i) E ^ 2 := by
    intro i
    have hb2 : b ^ 2 ≤ realStieltjes (μ i) E ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hb.le (hmod i) 2
    have hm := mul_le_mul_of_nonneg_left (hw i).2
      (show 0 ≤ b ^ 2 * ε ^ 2 by positivity)
    have hi : (b ^ 2 * ε ^ 2) * (ε⁻¹)^2 = b ^ 2 := by field_simp
    rw [hi] at hm
    exact hm.trans hb2
  have hh := Linear.real_axis_lower_norm_bound S
    (fun i => realStieltjes (μ i) E) (fun i => Poisson.weight (μ i) E)
    ((D⁻¹)^2) ((ε⁻¹)^2) (b^2 * ε^2) hS
    (by positivity) (by positivity) (by positivity)
    (fun i => (hw i).1) (fun i => (hw i).2) hd.2.2 hc u
  simpa only [stieltjes_real] using hh

theorem component_lower_from_bounds
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (T A R M : ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hz : ‖z‖ ≤ T) (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hmod : ∀ i, ‖m i‖ ≤ M) (hne : ∀ i, m i ≠ 0)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    (1 + T + A + R * M)⁻¹ ≤ ‖m i‖ := by
  have hs : (∑ j, S i j * ‖m j‖) ≤ R * M := by
    calc
      _ ≤ ∑ j, S i j * M := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hmod j) (hS i j))
      _ = (∑ j, S i j) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ R * M := mul_le_mul_of_nonneg_right (hrow i) hM
  have hi := ComponentBounds.inverse_norm_le hS hsol i
  have hK : 0 < 1 + T + A + R * M := by positivity
  apply (inv_le_comm₀ (norm_pos_iff.mpr (hne i)) hK).mp
  linarith [ha i]

/-- Uniform off-support coercivity for bounded real energies, including
height zero. The derivative weight, real inverse bound, small-height
perturbation, middle rectangle and large-height bound are all supplied by
proved lemmas; no inverse estimate is assumed here. -/
theorem bounded_exterior_uniform_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (hS : ∀ i j, 0 ≤ S i j)
    (T A R ε D : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hε : 0 < ε) (hD : 0 < D)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ E η : ℝ, |E| ≤ T → 0 ≤ η →
      (∀ i, ∀ᵐ t ∂μ i, ε ≤ |t-E|) →
      (∀ i, ∀ᵐ t ∂μ i, |t-E| ≤ D) →
      ∀ u : ι → ℂ, ‖u‖ ≤ C * ‖InteriorStability.stabilityOperator S
        (fun i => Poisson.stieltjes (μ i) (Poisson.point E η)) u‖ := by
  letI : ∀ i, IsProbabilityMeasure (μ i) := hμ
  let b := (1 + T + A + R * ε⁻¹)⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  let C₀ := (ε⁻¹)^2 / ((D⁻¹)^2 * (b^2 * ε^2))
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let K := 1 + 2 * ε⁻¹ * R * (ε⁻¹)^2
  have hK : 0 < K := by dsimp [K]; positivity
  let h := min 1 (1 / (2 * C₀ * K))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  let H := 1 + 2 * R
  have hH : h ≤ H := (min_le_left _ _).trans (by dsimp [H]; linarith)
  obtain ⟨C₁, hC₁, hmid⟩ := Linear.middle_rectangle_lower_norm_bound S a T h H hS hT hh hH
  let C := max 2 (max (2 * C₀) C₁)
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_left _ _), ?_⟩
  intro E η hE hη hgap hfar u
  let m₀ : ι → ℂ := fun i => Poisson.stieltjes (μ i) (Poisson.point E 0)
  let mη : ι → ℂ := fun i => Poisson.stieltjes (μ i) (Poisson.point E η)
  have hmods (s : ℝ) (i : ι) : ‖Poisson.stieltjes (μ i) (Poisson.point E s)‖ ≤ ε⁻¹ :=
    Poisson.stieltjes_norm_of_gap (μ i) hε (hgap i)
  have hd := measure_boundary_dyson_data S a μ hμ E ε hε hgap hupper hsol
  have hm₀ : ∀ i, b ≤ |realStieltjes (μ i) E| := by
    intro i
    have hh := component_lower_from_bounds S a (E : ℂ)
      (fun i => (realStieltjes (μ i) E : ℂ)) T A R ε⁻¹ hS hT hA hR
      (inv_nonneg.mpr hε.le) (by simpa using hE) ha hrow
      (fun i => by simpa [stieltjes_real] using hmods 0 i)
      (fun i => by
        change (realStieltjes (μ i) E : ℂ) ≠ 0
        exact_mod_cast hd.2.1 i) hd.1 i
    simpa [b] using hh
  have hbase : ∀ u : ι → ℂ, ‖u‖ ≤ C₀ * ‖InteriorStability.stabilityOperator S m₀ u‖ :=
    real_axis_measure_bound S a μ hμ hS E ε D b hε hD hb hgap hfar hm₀ hupper hsol
  by_cases hsmall : η ≤ h
  · have heps : C₀ * (K * η) ≤ 1/2 := by
      have hηbound : η ≤ 1 / (2 * C₀ * K) := hsmall.trans (min_le_right _ _)
      have hh' := (le_div_iff₀ (show 0 < 2*C₀*K by positivity)).mp hηbound
      nlinarith
    have hclose : ∀ u : ι → ℂ,
        ‖InteriorStability.stabilityOperator S m₀ u -
          InteriorStability.stabilityOperator S mη u‖ ≤ (K * η) * ‖u‖ := by
      intro v
      have hdelta : ∀ i, ‖m₀ i - mη i‖ ≤ η * (ε⁻¹)^2 := by
        intro i
        rw [norm_sub_rev]
        exact Poisson.stieltjes_difference_norm (μ i) hε hη (hgap i)
      have hl := Linear.stability_difference_bound S m₀ mη v ε⁻¹ R
        (η * (ε⁻¹)^2) hS (inv_nonneg.mpr hε.le) hR (by positivity)
        (hmods 0) (hmods η) hrow hdelta
      apply hl.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [K]
      nlinarith
    have hv := Norms.perturbation_lower_bound
      (InteriorStability.stabilityOperator S m₀) (InteriorStability.stabilityOperator S mη)
      C₀ (K*η) hC₀.le (by linarith) hbase hclose u
    have hconst : C₀ / (1 - C₀*(K*η)) ≤ 2*C₀ := by
      apply (div_le_iff₀ (by linarith : 0 < 1-C₀*(K*η))).mpr
      nlinarith
    exact hv.trans ((mul_le_mul_of_nonneg_right hconst (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right ((le_max_left (2*C₀) C₁).trans (le_max_right 2 _)) (norm_nonneg _)))
  · have hηpos : 0 < η := hh.trans (lt_of_not_ge hsmall)
    by_cases hmiddle : η ≤ H
    · have hv := hmid (Poisson.point E η) mη (by simpa [Poisson.point] using hE)
        (le_of_lt (lt_of_not_ge hsmall)) hmiddle
        (hupper _ hηpos) (hsol _ hηpos) u
      exact hv.trans (mul_le_mul_of_nonneg_right
        ((le_max_right (2*C₀) C₁).trans (le_max_right 2 _)) (norm_nonneg _))
    · have hηH : H < η := lt_of_not_ge hmiddle
      have hrowhigh : ∀ i, 2 * ∑ j, S i j ≤ (Poisson.point E η).im ^ 2 := by
        intro i
        change 2 * ∑ j, S i j ≤ η^2
        have hH2 : 2*R ≤ H^2 := by dsimp [H]; nlinarith
        have hs : H^2 ≤ η^2 := pow_le_pow_left₀ (by dsimp [H]; positivity) hηH.le 2
        linarith [hrow i]
      have hv := Linear.high_height_lower_norm_bound S a (Poisson.point E η) mη
        hS hηpos (hupper _ hηpos) (hsol _ hηpos) hrowhigh u
      exact hv.trans (mul_le_mul_of_nonneg_right (le_max_left 2 _) (norm_nonneg _))

/-- The complete uniform off-support estimate, with no bound on the real
energy or on the height. The support gap is expressed by an almost-everywhere
inequality, so it is insensitive to null sets in measure representatives. -/
theorem exterior_uniform_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) (hS : ∀ i j, 0 ≤ S i j)
    (A R Sigma ε : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hSigma : 0 ≤ Sigma) (hε : 0 < ε)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hsupport : ∀ i, ∀ᵐ t ∂μ i, |t| ≤ Sigma)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ E η : ℝ, 0 ≤ η →
      (∀ i, ∀ᵐ t ∂μ i, ε ≤ |t-E|) →
      ∀ u : ι → ℂ, ‖u‖ ≤ C * ‖InteriorStability.stabilityOperator S
        (fun i => Poisson.stieltjes (μ i) (Poisson.point E η)) u‖ := by
  letI : ∀ i, IsProbabilityMeasure (μ i) := hμ
  let T := Sigma + 1 + 2 * R
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let D := 1 + T + Sigma
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨C, hC, hbounded⟩ := bounded_exterior_uniform_bound S a μ hμ hS
    T A R ε D hT hA hR hε hD ha hrow hupper hsol
  refine ⟨max C 2, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro E η hη hgap u
  by_cases hE : |E| ≤ T
  · have hfar : ∀ i, ∀ᵐ t ∂μ i, |t-E| ≤ D := by
      intro i
      filter_upwards [hsupport i] with t ht
      have hh := abs_sub t E
      dsimp [D]
      linarith
    exact (hbounded E η hE hη hgap hfar u).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 2) (norm_nonneg _))
  · let δ := 1 + 2 * R
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hfar : ∀ i, ∀ᵐ t ∂μ i, δ ≤ |t-E| := by
      intro i
      filter_upwards [hsupport i] with t ht
      have he : T < |E| := lt_of_not_ge hE
      have hh : |E| ≤ |t| + |t-E| := by
        calc
          |E| = |t - (t-E)| := by congr 1; ring
          _ ≤ _ := abs_sub t (t-E)
      dsimp [T] at he
      dsimp [δ]
      linarith
    have hmod i : ‖Poisson.stieltjes (μ i) (Poisson.point E η)‖ ≤ δ⁻¹ :=
      Poisson.stieltjes_norm_of_gap (μ i) hδ (hfar i)
    have hsmall : ∀ i, ‖Poisson.stieltjes (μ i) (Poisson.point E η)‖^2 *
        ∑ j, S i j ≤ 1/2 := by
      intro i
      calc
        _ ≤ (δ⁻¹)^2 * R := mul_le_mul
          (pow_le_pow_left₀ (norm_nonneg _) (hmod i) 2) (hrow i)
          (Finset.sum_nonneg fun j _ => hS i j) (sq_nonneg _)
        _ = R / δ^2 := by ring
        _ ≤ 1/2 := by
          apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
          dsimp [δ]
          nlinarith
    have hv := Linear.row_lower_norm_bound S
      (fun i => Poisson.stieltjes (μ i) (Poisson.point E η)) (1/2)
      hS (by norm_num) hsmall u
    have htwo : ‖u‖ ≤ 2 * ‖InteriorStability.stabilityOperator S
        (fun i => Poisson.stieltjes (μ i) (Poisson.point E η)) u‖ := by
      norm_num at hv ⊢
      linarith
    exact htwo.trans (mul_le_mul_of_nonneg_right (le_max_right C 2) (norm_nonneg _))

end NonSymmetricDyson.Full.OffSupport
