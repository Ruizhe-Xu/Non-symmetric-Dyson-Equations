import Dyson.Full.Singularities

noncomputable section
open Filter
open scoped Topology

namespace NonSymmetricDyson.Full.Singularities

variable {ι : Type*} [Fintype ι]

theorem normalizedNonlinearity_conjugate
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (p q h ξ : ι → ℂ)
    (hF : ∀ x, F (star x) = star (F x)) (hp : star p = p) (hq : star q = q) :
    normalizedNonlinearity F.toLinearMap p q (star h) (star ξ) =
      star (normalizedNonlinearity F.toLinearMap p q h ξ) := by
  ext i
  have hpi : star (p i) = p i := congrFun hp i
  have hqi : star (q i) = q i := congrFun hq i
  simp [normalizedNonlinearity, hF, hpi, hqi]

/-- Reflection of the actual analytic solution curve follows from local
uniqueness and conjugation of its real-coefficient polynomial residual. -/
theorem exists_real_analytic_parametrization
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hFreal : ∀ x, F (star x) = star (F x))
    (hℓreal : ∀ x, ℓ (star x) = star (ℓ x)) (hp : star p = p) (hq : star q = q) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      (∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
          curve (ℓ v.2) = v) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), curve (star θ) = star (curve θ)) := by
  obtain ⟨curve, hca, hc0, hc, huniq⟩ :=
    exists_normalized_analytic_parametrization F ℓ p q r hμ hlF hsimple
  have hstar : Tendsto (fun θ => star (curve θ)) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [hc0, star_zero] using hca.continuousAt.star.tendsto
  refine ⟨curve, hca, hc0, hc, huniq, ?_⟩
  filter_upwards [hc, hstar.eventually huniq] with θ hθ hu
  have hres : (star (curve θ)).2 - F (star (curve θ)).2 =
      normalizedNonlinearity F.toLinearMap p q (star (curve θ)).2
        (fun _ => (star (curve θ)).1) := by
    have hh := congrArg star hθ.2
    simpa only [star_sub, ← hFreal, ← normalizedNonlinearity_conjugate F p q _ _ hFreal hp hq]
      using hh
  have hh := hu hres
  change curve (ℓ (star (curve θ).2)) = star (curve θ) at hh
  rw [hℓreal, hθ.1] at hh
  exact hh

/-- Real-axis preservation is the immediate boundary consequence of
reflection. -/
theorem complex_real_of_fixed_conjugate (z : ℂ) (hz : star z = z) : z.im = 0 := by
  have hh := congrArg Complex.im hz
  simp only [Complex.star_def, Complex.conj_im] at hh
  linarith

def RealAnalyticGerm (f : ℂ → ℂ) : Prop :=
  ∀ᶠ z in 𝓝 (0 : ℂ), f (star z) = star (f z)

/-- Standard local orientation preservation for a real analytic holomorphic
coordinate with derivative one. This external principle is quantified over
arbitrary scalar analytic functions and contains no Dyson assertion. -/
def RealHolomorphicOrientationPrinciple : Prop :=
  ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 → f 0 = 0 → HasDerivAt f 1 0 → RealAnalyticGerm f →
    ∀ᶠ z in 𝓝 (0 : ℂ), (0 < (f z).im ↔ 0 < z.im) ∧ ((f z).im = 0 ↔ z.im = 0)

/-- The normalized Perron coordinate of every genuine upper-half-plane
vector has positive imaginary part. This supplies the physical sign used in
the coordinate change; it is not a root-selection assumption. -/
theorem perronCoordinate_im_positive [Nonempty ι]
    (l q m : ι → ℝ) (u : ι → ℂ)
    (hl : ∀ i, 0 < l i) (hq : ∀ i, 0 < q i) (hu : ∀ i, 0 < (u i).im) :
    0 < (perronCoordinate (fun i => (l i : ℂ)) (fun i => (q i : ℂ))
      (fun i => (m i : ℂ)) u).im := by
  simp only [perronCoordinate, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.div_ofReal_im, Complex.sub_im, sub_zero]
  exact Finset.sum_pos (fun i _ => mul_pos (hl i) (div_pos (hu i) (hq i))) Finset.univ_nonempty

/-- An actual physical coordinate is transported to the positive-imaginary
root of the exact monomial chart. Local inversion and every neighborhood
restriction are verified; no continuity-of-branch label is assumed. -/
theorem physical_coordinate_monomial_matching
    (orientation : RealHolomorphicOrientationPrinciple)
    (Ω χ : ℂ → ℂ) (c : ℂ) (k : ℕ)
    (hχa : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) (hχd : HasDerivAt χ 1 0)
    (hχreal : RealAnalyticGerm χ)
    (hform : ∀ᶠ s in 𝓝 (0 : ℂ), Ω (χ s) = c * s ^ k)
    {α : Type*} (L : Filter α) (Θ w : α → ℂ)
    (hΘ : Tendsto Θ L (𝓝 0))
    (hphysical : ∀ᶠ a in L, 0 < (Θ a).im)
    (hgraph : ∀ᶠ a in L, w a = Ω (Θ a)) :
    ∃ s : α → ℂ, Tendsto s L (𝓝 0) ∧
      ∀ᶠ a in L, χ (s a) = Θ a ∧ w a = c * s a ^ k ∧ 0 < (s a).im := by
  have hsder : HasStrictDerivAt χ 1 0 := by
    have hh := hχa.hasStrictFDerivAt.hasStrictDerivAt
    have he := hh.hasDerivAt.unique hχd
    simpa only [he] using hh
  have hequiv := hsder.hasStrictFDerivAt_equiv (by norm_num : (1 : ℂ) ≠ 0)
  let inv := hequiv.localInverse χ _ 0
  have hinvt : Tendsto inv (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [hχ0] using hequiv.localInverse_tendsto
  have hright : ∀ᶠ θ in 𝓝 (0 : ℂ), χ (inv θ) = θ := by
    simpa only [hχ0] using hequiv.eventually_right_inverse
  let s : α → ℂ := inv ∘ Θ
  have hst : Tendsto s L (𝓝 0) := hinvt.comp hΘ
  refine ⟨s, hst, ?_⟩
  filter_upwards [hΘ.eventually hright, hst.eventually hform,
    hst.eventually (orientation χ hχa hχ0 hχd hχreal), hphysical, hgraph]
      with a ha hfa hoa hpa hga
  change χ (s a) = Θ a at ha
  refine ⟨ha, ?_, ?_⟩
  · rw [hga, ← ha]
    exact hfa
  · exact hoa.1.mp (by simpa only [ha] using hpa)

/-- The tangent of the actual normalized analytic solution curve is `(0,r)`.
The derivative in energy vanishes and the vector derivative is the Perron
vector; this follows by differentiating the already verified augmented map. -/
theorem normalized_solution_curve_tangent
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0) (hFr : F r = r) (hnorm : ℓ r = 1)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (curve : ℂ → ℂ × (ι → ℂ)) (hca : AnalyticAt ℂ curve 0) (hc0 : curve 0 = 0)
    (hc : ∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
      (curve θ).2 - F (curve θ).2 =
        normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) :
    HasDerivAt curve (0, r) 0 := by
  have hd : HasDerivAt curve (deriv curve 0) 0 := hca.differentiableAt.hasDerivAt
  have hf := (normalizedAugmentedMap_hasStrictFDerivAt F ℓ p q).hasFDerivAt
  have hcomp := hf.comp_hasDerivAt_of_eq 0 hd hc0.symm
  have hembed : HasDerivAt (fun θ : ℂ => (θ, (0 : ι → ℂ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have heq : (normalizedAugmentedMap F ℓ p q ∘ curve) =ᶠ[𝓝 (0 : ℂ)]
      (fun θ => (θ, (0 : ι → ℂ))) := by
    filter_upwards [hc] with θ hθ
    exact Prod.ext hθ.1 (sub_eq_zero.mpr hθ.2)
  have hj := hcomp.unique (hembed.congr_of_eventuallyEq heq)
  have hr : augmentedDerivative F ℓ q (0, r) = (1, 0) := by
    simp [hFr, hnorm]
  have ht : deriv curve 0 = (0, r) :=
    (augmentedDerivative_bijective F ℓ q r hμ hlF hsimple).1 (hj.trans hr.symm)
  simpa only [ht] using hd

end NonSymmetricDyson.Full.Singularities
