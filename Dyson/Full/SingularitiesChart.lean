import Dyson.Full.SingularitiesMatching

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Assembly from real Perron data: all analytic curve equations, the exact
physical root matching, the positive tangent and Taylor error are proved.
The following actual-frontier theorem supplies every matrix datum internally. -/
theorem physical_normal_form_of_perron_data_with_degree
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (S F : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ)
    (m₀ p q r l u : ι → ℝ)
    (K : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m₀ i)
    (hqpos : ∀ i, 0 < q i) (hrpos : ∀ i, 0 < r i) (hlpos : ∀ i, 0 < l i)
    (hF : ∀ i j, F i j = q i * S i j * q j)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j) (hnorm : ∑ i, l i * r i = 1)
    (hsimple : ∀ x : ι → ℂ, complexMatrixOperator F x = x →
      x = complexFunctional l x • (fun i => (r i : ℂ)))
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K
      (complexFunctional l).toLinearMap (fun i => (r i : ℂ)))
    (hσ : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ)^2) =
      (quadraticCoefficient p l r : ℂ))
    (hψ : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ) *
      (complexMatrixOperator F (K (fun j => (p j : ℂ) * (r j : ℂ)^2)) i +
        K (fun j => (p j : ℂ) * (r j : ℂ)^2) i)) =
      (cubicCoefficient F p l r u : ℂ))
    (hnd : quadraticCoefficient p l r ≠ 0 ∨ 0 < cubicCoefficient F p l r u)
    (hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ) (fun i => (m₀ i : ℂ)))
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 (fun i => (m₀ i : ℂ)))) :
    ∃ P : PhysicalNormalForm S a τ m m₀,
      (quadraticCoefficient p l r ≠ 0 → P.degree = 2) ∧
      (quadraticCoefficient p l r = 0 → P.degree = 3) := by
  let μ : ℝ := ∑ i, l i * q i
  have hμpos : 0 < μ :=
    Finset.sum_pos (fun i _ => mul_pos (hlpos i) (hqpos i)) Finset.univ_nonempty
  have hμeq : complexFunctional l (fun i => (q i : ℂ)) = (μ : ℂ) := by
    simp [complexFunctional_apply, μ]
  have hFrC : complexMatrixOperator F (fun i => (r i : ℂ)) = (fun i => (r i : ℂ)) := by
    ext i
    simp only [complexMatrixOperator_apply]
    exact_mod_cast hFr i
  have hnormC : complexFunctional l (fun i => (r i : ℂ)) = 1 := by
    rw [complexFunctional_apply]
    exact_mod_cast hnorm
  have hFreal : ∀ x, complexMatrixOperator F (star x) = star (complexMatrixOperator F x) := by
    intro x
    ext i
    simp [complexMatrixOperator_apply]
  have hℓreal : ∀ x, complexFunctional l (star x) = star (complexFunctional l x) := by
    intro x
    simp [complexFunctional_apply]
  have hσ' : complexFunctional l ((fun i => (p i : ℂ)) * (fun i => (r i : ℂ)) *
      (fun i => (r i : ℂ))) = (quadraticCoefficient p l r : ℂ) := by
    simpa only [pow_two, mul_assoc] using hσ
  have hψ' : complexFunctional l ((fun i => (p i : ℂ)) * (fun i => (r i : ℂ)) *
      (complexMatrixOperator F (K ((fun i => (p i : ℂ)) * (fun i => (r i : ℂ)) *
        (fun i => (r i : ℂ)))) + K ((fun i => (p i : ℂ)) * (fun i => (r i : ℂ)) *
          (fun i => (r i : ℂ))))) = (cubicCoefficient F p l r u : ℂ) := by
    simpa only [pow_two, mul_assoc] using hψ
  obtain ⟨C, k, c, χ, hCa, hC0, hCd, hCeq, huniq, hCreal,
      hχa, hχ0, hχd, hχreal, hform, hcases⟩ :=
    normalized_system_real_chart normalForm (complexMatrixOperator F) K.toContinuousLinearMap
      (complexFunctional l) (fun i => (p i : ℂ)) (fun i => (q i : ℂ))
      (fun i => (r i : ℂ)) μ hμpos hμeq hFrC hnormC
      (complexFunctional_left_eigenvector F l hlF) hsimple hK hFreal hℓreal
      (by ext i; simp) (by ext i; simp)
      (quadraticCoefficient p l r) (cubicCoefficient F p l r u) hσ' hψ' hnd
  have hFscaled : ∀ h, complexMatrixOperator F h =
      DysonPaper.Algebra.scaledOperator (fun i => (q i : ℂ)) (Model.action S) h := by
    intro h
    ext i
    simp only [complexMatrixOperator_apply, hF, Complex.ofReal_mul,
      DysonPaper.Algebra.scaledOperator, DysonPaper.Algebra.coordMul,
      Model.action_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  let M : ℂ → ι → ℂ := fun s i => (m₀ i : ℂ) + (q i : ℂ) * (C (χ s)).2 i
  have hMa : AnalyticAt ℂ M 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact analyticAt_const.add (analyticAt_const.mul
      ((((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)).analyticAt _).comp
        (((ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)).analyticAt _).comp
          (hCa.comp_of_eq hχa hχ0))))
  have hMd : HasDerivAt M (fun i => ((q i * r i : ℝ) : ℂ)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hcomp : HasDerivAt (fun s => C (χ s)) (0, fun i => (r i : ℂ)) 0 := by
      simpa using hCd.scomp_of_eq 0 hχd hχ0.symm
    simpa [M] using ((hasDerivAt_pi.mp hcomp.snd) i).const_mul (q i : ℂ) |>.const_add (m₀ i : ℂ)
  obtain ⟨B, hB, hTaylor⟩ := physical_curve_taylor_bound C χ m₀ q r hCa hC0 hCd hχa hχ0 hχd
  obtain ⟨s, hst, hphysical⟩ := physical_family_matches_chart orientation S a τ m₀ p q l
    (complexMatrixOperator F) hp hq hqpos hlpos hFscaled hbase m hupper heq hlim
    C huniq χ k c hχa hχ0 hχd hχreal hform
  have hχt : Tendsto χ (𝓝 (0 : ℂ)) (𝓝 0) := by simpa only [hχ0] using hχa.continuousAt.tendsto
  have heqM : ∀ᶠ s in 𝓝 (0 : ℂ), PolynomialDyson.IsPolynomialSolution S a
      ((τ : ℂ) + (c : ℂ) * s ^ k) (M s) := by
    filter_upwards [hχt.eventually hCeq, hform] with s hs hf
    rw [← hf]
    exact SingularLinear.normalized_residual_polynomial_solution S a (τ : ℂ) (C (χ s)).1
      (fun i => (m₀ i : ℂ)) (fun i => (p i : ℂ)) (fun i => (q i : ℂ)) (C (χ s)).2
      (complexMatrixOperator F) (fun i => by dsimp; exact_mod_cast hp i)
      (fun i => by dsimp; exact_mod_cast hq i) hFscaled hbase hs.2
  have hMreal : ∀ᶠ s in 𝓝 (0 : ℂ), M (star s) = star (M s) := by
    filter_upwards [hχreal, hχt.eventually hCreal] with s hs hc
    ext i
    simp only [M, hs, hc, Pi.star_apply]
    simp
  have hk : k = 2 ∨ k = 3 := hcases.imp And.left And.left
  have hcne : c ≠ 0 := by
    rcases hcases with ⟨_, hσne, rfl⟩ | ⟨_, _, hψpos, rfl⟩
    · exact neg_ne_zero.mpr (div_ne_zero hσne hμpos.ne')
    · exact neg_ne_zero.mpr (div_ne_zero hψpos.ne' hμpos.ne')
  have hcubic : k = 3 → c < 0 := by
    intro hk3
    rcases hcases with ⟨hk2, _, _⟩ | ⟨_, _, hψpos, rfl⟩
    · omega
    · exact neg_neg_of_pos (div_pos hψpos hμpos)
  refine ⟨{
    degree := k, coefficient := c, curve := M, parameter := s,
    tangent := fun i => q i * r i, errorConstant := B,
    degree_cases := hk, coefficient_ne_zero := hcne, cubic_negative := hcubic,
    analytic := hMa, base := by ext i; simp [M, hχ0, hC0], derivative := hMd,
    tangent_pos := fun i => mul_pos (hqpos i) (hrpos i), errorConstant_pos := hB,
    equation := heqM, reflection := hMreal, parameter_limit := hst,
    physical := hphysical, taylor := hTaylor }, ?_, ?_⟩
  · intro hσne
    rcases hcases with h | h
    · exact h.1
    · exact False.elim (hσne h.2.1)
  · intro hσzero
    rcases hcases with h | h
    · exact False.elim (h.2.1 hσzero)
    · exact h.1

theorem physical_normal_form_of_perron_data
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (S F : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ)
    (m₀ p q r l u : ι → ℝ)
    (K : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m₀ i)
    (hqpos : ∀ i, 0 < q i) (hrpos : ∀ i, 0 < r i) (hlpos : ∀ i, 0 < l i)
    (hF : ∀ i j, F i j = q i * S i j * q j)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j) (hnorm : ∑ i, l i * r i = 1)
    (hsimple : ∀ x : ι → ℂ, complexMatrixOperator F x = x →
      x = complexFunctional l x • (fun i => (r i : ℂ)))
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K
      (complexFunctional l).toLinearMap (fun i => (r i : ℂ)))
    (hσ : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ)^2) =
      (quadraticCoefficient p l r : ℂ))
    (hψ : complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ) *
      (complexMatrixOperator F (K (fun j => (p j : ℂ) * (r j : ℂ)^2)) i +
        K (fun j => (p j : ℂ) * (r j : ℂ)^2) i)) =
      (cubicCoefficient F p l r u : ℂ))
    (hnd : quadraticCoefficient p l r ≠ 0 ∨ 0 < cubicCoefficient F p l r u)
    (hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ) (fun i => (m₀ i : ℂ)))
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 (fun i => (m₀ i : ℂ)))) :
    Nonempty (PhysicalNormalForm S a τ m m₀) := by
  obtain ⟨P, _, _⟩ := physical_normal_form_of_perron_data_with_degree normalForm orientation
    S F a τ m₀ p q r l u K hp hq hqpos hrpos hlpos hF hFr hlF hnorm hsimple hK
    hσ hψ hnd hbase m hupper heq hlim
  exact ⟨P⟩

end NonSymmetricDyson.Full.Singularities
