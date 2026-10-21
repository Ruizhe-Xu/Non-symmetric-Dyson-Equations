import Dyson.Full.SingularitiesBoundaryChart
import Dyson.Full.SingularitiesRootGeometry

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The positive modulus of the exact degree-k monomial parameter. -/
def rootRadius (c : ℝ) (k : ℕ) (w : ℝ) : ℝ := (|w| / |c|) ^ ((k : ℝ)⁻¹)

/-- The cubic chart gives the two-sided cusp law for the true boundary
values. Its coefficient is positive, and both punctured sides have positive
density. -/
theorem PhysicalNormalForm.cubic_boundary_density
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) (hk : P.degree = 3)
    (b : ℝ → ι → ℂ) (hb0 : b τ = (fun i => (m₀ i : ℂ)))
    (hbcont : ContinuousAt b τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ, Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (b x))) :
    ∀ᶠ x in 𝓝 τ, ∀ i,
      |(b x i).im - P.tangent i * (Real.sqrt 3 / 2) * rootRadius P.coefficient 3 (x - τ)| ≤
        P.errorConstant * (rootRadius P.coefficient 3 (x - τ)) ^ 2 ∧
      (x ≠ τ → 0 < (b x i).im) := by
  obtain ⟨t, ht, hrepr⟩ := P.boundary_representation b hb0 hbcont hblim
  have hsmall : ∀ᶠ x in 𝓝 τ, ∀ i,
      P.errorConstant * ‖t x‖ ≤ (P.tangent i * (Real.sqrt 3 / 2)) / 2 := by
    apply Filter.eventually_all.mpr
    intro i
    have hpos : 0 < (P.tangent i * (Real.sqrt 3 / 2)) / 2 := by
      exact div_pos (mul_pos (P.tangent_pos i) (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))) (by norm_num)
    have hh := (tendsto_const_nhds.mul ht.norm).eventually_lt_const
      (show P.errorConstant * ‖(0 : ℂ)‖ < (P.tangent i * (Real.sqrt 3 / 2)) / 2 by simpa using hpos)
    exact hh.mono fun x hx => hx.le
  filter_upwards [hrepr, ht.eventually P.taylor, hsmall] with x hx hTaylor hs i
  have hroot : ((x - τ : ℝ) : ℂ) = (P.coefficient : ℂ) * t x ^ 3 := by
    simpa only [hk] using hx.2.1
  have hreal : ((t x) ^ 3).im = 0 := by
    have hh := congrArg Complex.im hroot
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left P.coefficient_ne_zero
  have him := cubic_boundary_im_norm (t x) hx.2.2.1 (hx.2.2.2 hk) hreal
  have hnorm : ‖t x‖ = rootRadius P.coefficient 3 (x - τ) :=
    monomial_parameter_norm P.coefficient (x - τ) (t x) 3 P.coefficient_ne_zero (by norm_num) hroot
  have herr := imaginary_taylor_remainder_bound (P.curve (t x) i) (t x)
    (m₀ i) (P.tangent i) P.errorConstant (hTaylor i)
  have herr' : |(b x i).im - (P.tangent i * (Real.sqrt 3 / 2)) * ‖t x‖| ≤
      P.errorConstant * ‖t x‖ ^ 2 := by
    simpa only [hx.1, him, mul_assoc] using herr
  refine ⟨by simpa only [hnorm] using herr', ?_⟩
  intro hne
  have htne : t x ≠ 0 := by
    intro hz
    have hh : x - τ = 0 := by
      have hh := congrArg Complex.re hroot
      simpa [hz] using hh
    exact hne (sub_eq_zero.mp hh)
  have hD : 0 < P.tangent i * (Real.sqrt 3 / 2) :=
    mul_pos (P.tangent_pos i) (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
  have hlo := (positive_density_scale (b x i).im (P.tangent i * (Real.sqrt 3 / 2))
    P.errorConstant ‖t x‖ (norm_nonneg _) hD herr' (hs i)).1
  exact lt_of_lt_of_le (mul_pos (half_pos hD) (norm_pos_iff.mpr htne)) hlo

/-- The quadratic chart gives precisely one interior square-root side and
an exactly zero exterior density. The interior coefficient is positive. -/
theorem PhysicalNormalForm.quadratic_boundary_density
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) (hk : P.degree = 2)
    (b : ℝ → ι → ℂ) (hb0 : b τ = (fun i => (m₀ i : ℂ)))
    (hbcont : ContinuousAt b τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ, Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (b x))) :
    ∀ᶠ x in 𝓝 τ, ∀ i,
      (P.coefficient * (x - τ) < 0 →
        |(b x i).im - P.tangent i * rootRadius P.coefficient 2 (x - τ)| ≤
          P.errorConstant * (rootRadius P.coefficient 2 (x - τ)) ^ 2 ∧ 0 < (b x i).im) ∧
      (0 < P.coefficient * (x - τ) → (b x i).im = 0) := by
  obtain ⟨t, ht, hrepr⟩ := P.boundary_representation b hb0 hbcont hblim
  have hsmall : ∀ᶠ x in 𝓝 τ, ∀ i, P.errorConstant * ‖t x‖ ≤ P.tangent i / 2 := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := (tendsto_const_nhds.mul ht.norm).eventually_lt_const
      (show P.errorConstant * ‖(0 : ℂ)‖ < P.tangent i / 2 by simpa using half_pos (P.tangent_pos i))
    exact hh.mono fun x hx => hx.le
  filter_upwards [hrepr, ht.eventually P.taylor, ht.eventually P.reflection, hsmall]
    with x hx hTaylor href hs i
  have hroot : ((x - τ : ℝ) : ℂ) = (P.coefficient : ℂ) * t x ^ 2 := by
    simpa only [hk] using hx.2.1
  constructor
  · intro hside
    have him := square_boundary_inside_im_norm P.coefficient (x - τ) (t x)
      P.coefficient_ne_zero hx.2.2.1 hside hroot
    have hnorm : ‖t x‖ = rootRadius P.coefficient 2 (x - τ) :=
      monomial_parameter_norm P.coefficient (x - τ) (t x) 2 P.coefficient_ne_zero (by norm_num) hroot
    have herr := imaginary_taylor_remainder_bound (P.curve (t x) i) (t x)
      (m₀ i) (P.tangent i) P.errorConstant (hTaylor i)
    have herr' : |(b x i).im - P.tangent i * ‖t x‖| ≤ P.errorConstant * ‖t x‖ ^ 2 := by
      simpa only [hx.1, him] using herr
    refine ⟨by simpa only [hnorm] using herr', ?_⟩
    have htne : t x ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hroot
      have he : x - τ = 0 := by simpa [hz] using hh
      simp [he] at hside
    have hlo := (positive_density_scale (b x i).im (P.tangent i) P.errorConstant ‖t x‖
      (norm_nonneg _) (P.tangent_pos i) herr' (hs i)).1
    exact lt_of_lt_of_le (mul_pos (half_pos (P.tangent_pos i)) (norm_pos_iff.mpr htne)) hlo
  · intro hside
    have hi := square_boundary_outside_real P.coefficient (x - τ) (t x)
      P.coefficient_ne_zero hside hroot
    have hstar : star (t x) = t x := by
      apply Complex.ext <;> simp [hi]
    rw [hstar] at href
    have hh : star (P.curve (t x) i) = P.curve (t x) i := (congrFun href i).symm
    simpa only [hx.1] using complex_real_of_fixed_conjugate (P.curve (t x) i) hh

end NonSymmetricDyson.Full.Singularities
