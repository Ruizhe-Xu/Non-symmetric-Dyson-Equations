import Dyson.Full.SingularitiesTaylor
import Dyson.Full.SingularLinear
import Dyson.Full.ExternalAlgebraic

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Concrete normal form of the actual solution family. The parameter is
selected by its positive imaginary part; the analytic curve solves the
original Dyson equation and has a positive, explicitly bounded tangent. -/
structure PhysicalNormalForm (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ)
    (m : ℂ → ι → ℂ) (m₀ : ι → ℝ) where
  degree : ℕ
  coefficient : ℝ
  curve : ℂ → ι → ℂ
  parameter : ℂ → ℂ
  tangent : ι → ℝ
  errorConstant : ℝ
  degree_cases : degree = 2 ∨ degree = 3
  coefficient_ne_zero : coefficient ≠ 0
  cubic_negative : degree = 3 → coefficient < 0
  analytic : AnalyticAt ℂ curve 0
  base : curve 0 = (fun i => (m₀ i : ℂ))
  derivative : HasDerivAt curve (fun i => (tangent i : ℂ)) 0
  tangent_pos : ∀ i, 0 < tangent i
  errorConstant_pos : 0 < errorConstant
  equation : ∀ᶠ s in 𝓝 (0 : ℂ), PolynomialDyson.IsPolynomialSolution S a
    ((τ : ℂ) + (coefficient : ℂ) * s ^ degree) (curve s)
  reflection : ∀ᶠ s in 𝓝 (0 : ℂ), curve (star s) = star (curve s)
  parameter_limit : Tendsto parameter (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 0)
  physical : ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (τ : ℂ),
    m z = curve (parameter z) ∧ z - (τ : ℂ) = (coefficient : ℂ) * parameter z ^ degree ∧
      0 < (parameter z).im
  taylor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ i,
    ‖curve s i - (m₀ i : ℂ) - (tangent i : ℂ) * s‖ ≤ errorConstant * ‖s‖ ^ 2

/-- The parameter of every actual physical family is the positive-imaginary
root in its real monomial chart. Every matching step uses the original
polynomial equation and the local uniqueness already proved by the IFT. -/
theorem physical_family_matches_chart
    (orientation : RealHolomorphicOrientationPrinciple)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ)
    (m₀ p q l : ι → ℝ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m₀ i)
    (hqpos : ∀ i, 0 < q i) (hlpos : ∀ i, 0 < l i)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator (fun i => (q i : ℂ)) (Model.action S) h)
    (hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ) (fun i => (m₀ i : ℂ)))
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 (fun i => (m₀ i : ℂ))))
    (curve : ℂ → ℂ × (ι → ℂ))
    (huniq : ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
      v.2 - F v.2 = normalizedNonlinearity F.toLinearMap
        (fun i => (p i : ℂ)) (fun i => (q i : ℂ)) v.2 (fun _ => v.1) →
        curve (complexFunctional l v.2) = v)
    (χ : ℂ → ℂ) (k : ℕ) (c : ℝ)
    (hχa : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) (hχd : HasDerivAt χ 1 0)
    (hχreal : RealAnalyticGerm χ)
    (hform : ∀ᶠ s in 𝓝 (0 : ℂ), (curve (χ s)).1 = (c : ℂ) * s ^ k) :
    ∃ s : ℂ → ℂ, Tendsto s (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 0) ∧
      ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (τ : ℂ),
        m z = (fun i => (m₀ i : ℂ) + (q i : ℂ) * (curve (χ (s z))).2 i) ∧
        z - (τ : ℂ) = (c : ℂ) * s z ^ k ∧ 0 < (s z).im := by
  let L := 𝓝[ExternalAlgebraic.upper] (τ : ℂ)
  let H : ℂ → ι → ℂ := fun z i => (m z i - (m₀ i : ℂ)) / (q i : ℂ)
  let V : ℂ → ℂ × (ι → ℂ) := fun z => (z - (τ : ℂ), H z)
  have hH : Tendsto H L (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hh := ((tendsto_pi_nhds.mp hlim i).sub_const (m₀ i : ℂ)).div_const (q i : ℂ)
    simpa only [sub_self, zero_div] using hh
  have hV : Tendsto V L (𝓝 0) := by
    have hz : Tendsto (fun z : ℂ => z - (τ : ℂ)) L (𝓝 0) := by
      simpa only [sub_self] using
        ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 (τ : ℂ)) (𝓝 (τ : ℂ))).mono_left
          nhdsWithin_le_nhds).sub_const (τ : ℂ)
    exact hz.prodMk_nhds hH
  have hΘ : Tendsto (fun z => complexFunctional l (H z)) L (𝓝 0) := by
    simpa only [map_zero] using (complexFunctional l).continuous.continuousAt.tendsto.comp hH
  have hcurve : ∀ᶠ z in L, curve (complexFunctional l (H z)) = V z := by
    filter_upwards [hV.eventually huniq, self_mem_nhdsWithin] with z hu hz
    apply hu
    apply polynomial_solution_normalized_residual S a (τ : ℂ) (z - (τ : ℂ))
      (fun i => (m₀ i : ℂ)) (m z) (fun i => (p i : ℂ)) (fun i => (q i : ℂ)) F
    · intro i; exact_mod_cast hp i
    · intro i; exact_mod_cast hq i
    · intro i; exact_mod_cast (hqpos i).ne'
    · exact hF
    · exact hbase
    · simpa only [add_sub_cancel] using
        PolynomialDyson.of_dyson (heq z hz) (BasicEstimates.component_ne_zero (hupper z hz))
  have hpositive : ∀ᶠ z in L, 0 < (complexFunctional l (H z)).im := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [perronCoordinate, complexFunctional_apply, H] using
      perronCoordinate_im_positive l q m₀ (m z) hlpos hqpos (hupper z hz)
  have hgraph : ∀ᶠ z in L, z - (τ : ℂ) = (curve (complexFunctional l (H z))).1 := by
    filter_upwards [hcurve] with z hz
    exact (congrArg Prod.fst hz).symm
  obtain ⟨s, hs, hmatch⟩ := physical_coordinate_monomial_matching orientation
    (fun θ => (curve θ).1) χ (c : ℂ) k hχa hχ0 hχd hχreal hform L
    (fun z => complexFunctional l (H z)) (fun z => z - (τ : ℂ)) hΘ hpositive hgraph
  refine ⟨s, hs, ?_⟩
  filter_upwards [hmatch, hcurve] with z hm hc
  refine ⟨?_, hm.2⟩
  rw [hm.1, hc]
  funext i
  change m z i = (m₀ i : ℂ) + (q i : ℂ) * ((m z i - (m₀ i : ℂ)) / (q i : ℂ))
  have hq0 : (q i : ℂ) ≠ 0 := by exact_mod_cast (hqpos i).ne'
  field_simp
  ring

end NonSymmetricDyson.Full.Singularities
