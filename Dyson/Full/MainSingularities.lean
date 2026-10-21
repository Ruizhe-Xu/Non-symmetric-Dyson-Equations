import Dyson.Full.SingularitiesChart
import Dyson.Full.SingularitiesFrontierData

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- The actual physical solution has a quadratic edge or a cubic cusp
normal form at every regular support frontier. Perron data, the restricted
inverse, the cubic coefficient and its nondegeneracy are all constructed from
the stated model and frontier hypotheses. No Dyson classification is an input. -/
theorem regular_frontier_physical_normal_form
    (perron : ExternalPerronExistence)
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
    (hτ : τ ∉ Boundary.singularUnion m) :
    Nonempty (PhysicalNormalForm S a τ m
      (fun j => (Boundary.boundaryVector m (τ : ℂ) j).re)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨D⟩ := regular_frontier_data perron hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  have hcast : (fun j => ((m₀ j).re : ℂ)) = m₀ := by
    ext j
    exact Complex.ext rfl (by simpa using (D.real_value j).symm)
  have hbe := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ)
      (fun j => ((m₀ j).re : ℂ)) := by
    rw [hcast]
    exact PolynomialDyson.of_dyson hbe.2.2 hbe.1
  have hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ))
      (𝓝 (fun j => ((m₀ j).re : ℂ))) := by
    rw [hcast]
    have hc := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      (τ : ℂ) (Or.inr ⟨τ, hτ, rfl⟩)
    have ht := (hc.mono (show ExternalAlgebraic.upper ⊆ Boundary.commonRegularDomain m
      from fun _ hz => Or.inl hz)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S a hS m hupper heq z hz
  exact physical_normal_form_of_perron_data normalForm orientation S (saturatedMatrix S m₀) a τ
    (fun j => (m₀ j).re) D.p (fun j => ‖m₀ j‖) D.r D.l D.u D.K
    D.sign_square D.norm_sign (fun j => norm_pos_iff.mpr (D.nonzero j))
    D.right_positive D.left_positive (fun _ _ => rfl) D.right_fixed D.left_fixed
    D.normalized D.simple D.restricted D.quadratic_bridge D.cubic_bridge D.nondegenerate
    hbase m hupper heq hlim

theorem frontier_data_physical_normal_form
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
    ∃ P : PhysicalNormalForm S a τ m (fun j => (Boundary.boundaryVector m (τ : ℂ) j).re),
      (quadraticCoefficient D.p D.l D.r ≠ 0 → P.degree = 2) ∧
      (quadraticCoefficient D.p D.l D.r = 0 → P.degree = 3) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  have hcast : (fun j => ((m₀ j).re : ℂ)) = m₀ := by
    ext j
    exact Complex.ext rfl (by simpa using (D.real_value j).symm)
  have hbe := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ)
      (fun j => ((m₀ j).re : ℂ)) := by
    rw [hcast]
    exact PolynomialDyson.of_dyson hbe.2.2 hbe.1
  have hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ))
      (𝓝 (fun j => ((m₀ j).re : ℂ))) := by
    rw [hcast]
    have hc := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      (τ : ℂ) (Or.inr ⟨τ, hτ, rfl⟩)
    have ht := (hc.mono (show ExternalAlgebraic.upper ⊆ Boundary.commonRegularDomain m
      from fun _ hz => Or.inl hz)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S a hS m hupper heq z hz
  exact physical_normal_form_of_perron_data_with_degree normalForm orientation S (saturatedMatrix S m₀) a τ
    (fun j => (m₀ j).re) D.p (fun j => ‖m₀ j‖) D.r D.l D.u D.K
    D.sign_square D.norm_sign (fun j => norm_pos_iff.mpr (D.nonzero j))
    D.right_positive D.left_positive (fun _ _ => rfl) D.right_fixed D.left_fixed
    D.normalized D.simple D.restricted D.quadratic_bridge D.cubic_bridge D.nondegenerate
    hbase m hupper heq hlim

end NonSymmetricDyson.Full.Singularities
