import Dyson.Full.MainSingularities

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual upper-half-plane chart extends to its finite real boundary.
The central cubic cone is retained under the limit, which excludes the
extraneous real cubic root. No density asymptotic is used. -/
theorem PhysicalNormalForm.boundary_representation
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀)
    (b : ℝ → ι → ℂ) (hb0 : b τ = (fun i => (m₀ i : ℂ)))
    (hbcont : ContinuousAt b τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ, Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (b x))) :
    ∃ t : ℝ → ℂ, Tendsto t (𝓝 τ) (𝓝 0) ∧
      ∀ᶠ x in 𝓝 τ, b x = P.curve (t x) ∧
        ((x - τ : ℝ) : ℂ) = (P.coefficient : ℂ) * t x ^ P.degree ∧
        0 ≤ (t x).im ∧
        (P.degree = 3 → 3 * (t x).re ^ 2 ≤ (t x).im ^ 2) := by
  classical
  let i : ι := Classical.arbitrary ι
  let d : ℂ := (P.tangent i : ℂ)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (P.tangent_pos i).ne'
  let f : ℂ → ℂ := fun s => (P.curve s i - (m₀ i : ℂ)) / d
  have hfa : AnalyticAt ℂ f 0 :=
    ((analyticAt_pi_iff.mp P.analytic i).sub analyticAt_const).div analyticAt_const hd
  have hf0 : f 0 = 0 := by simp [f, P.base]
  have hfd : HasDerivAt f 1 0 := by
    simpa only [d, div_self hd] using ((hasDerivAt_pi.mp P.derivative i).sub_const (m₀ i : ℂ)).div_const d
  have hfs : HasStrictDerivAt f 1 0 := by
    have hh := hfa.hasStrictFDerivAt.hasStrictDerivAt
    simpa only [hh.hasDerivAt.unique hfd] using hh
  have he := hfs.hasStrictFDerivAt_equiv (by norm_num : (1 : ℂ) ≠ 0)
  let inv := he.localInverse f _ 0
  have hinv0 : inv 0 = 0 := by simpa only [hf0] using he.localInverse_apply_image
  have hinva : AnalyticAt ℂ inv 0 := by
    have hh := (he.toOpenPartialHomeomorph f).analyticAt_symm'
      he.mem_toOpenPartialHomeomorph_source hfa he.hasFDerivAt.fderiv
    change AnalyticAt ℂ inv (f 0) at hh
    simpa only [hf0] using hh
  have hleft : ∀ᶠ s in 𝓝 (0 : ℂ), inv (f s) = s := he.eventually_left_inverse
  let X : ℂ → ℂ := fun z => (m z i - (m₀ i : ℂ)) / d
  let Y : ℝ → ℂ := fun x => (b x i - (m₀ i : ℂ)) / d
  let T : ℂ → ℂ := inv ∘ X
  let t : ℝ → ℂ := inv ∘ Y
  have hY : Tendsto Y (𝓝 τ) (𝓝 0) := by
    have hh := ((tendsto_pi_nhds.mp hbcont.tendsto i).sub_const (m₀ i : ℂ)).div_const d
    simpa only [hb0, sub_self, zero_div] using hh
  have ht : Tendsto t (𝓝 τ) (𝓝 0) := by
    have hit : Tendsto inv (𝓝 (0 : ℂ)) (𝓝 0) := by
      simpa only [hinv0] using hinva.continuousAt.tendsto
    exact hit.comp hY
  have hQ : ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (τ : ℂ),
      m z = P.curve (T z) ∧ z - (τ : ℂ) = (P.coefficient : ℂ) * T z ^ P.degree ∧
      0 < (T z).im ∧ (P.degree = 3 → 3 * (T z).re ^ 2 ≤ (T z).im ^ 2) := by
    filter_upwards [P.physical, P.parameter_limit.eventually hleft, self_mem_nhdsWithin]
      with z hp hl hz
    have hX : X z = f (P.parameter z) := by
      dsimp [X, f]
      rw [hp.1]
    have hT : T z = P.parameter z := by dsimp [T, Function.comp_def]; rw [hX]; exact hl
    rw [hT]
    refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
    intro hk
    apply (cubic_upper_central_cone _ hp.2.2 ?_).le
    have hh := congrArg Complex.im hp.2.1
    simp only [hk, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero] at hh
    have hc := P.cubic_negative hk
    have hz' : 0 < z.im := hz
    nlinarith
  have hQnear : ∀ᶠ x : ℝ in 𝓝 τ, ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (x : ℂ),
      m z = P.curve (T z) ∧ z - (τ : ℂ) = (P.coefficient : ℂ) * T z ^ P.degree ∧
      0 < (T z).im ∧ (P.degree = 3 → 3 * (T z).re ^ 2 ≤ (T z).im ^ 2) :=
    Complex.continuous_ofReal.continuousAt.tendsto.eventually
      (eventually_nhds_nhdsWithin.mpr hQ)
  refine ⟨t, ht, ?_⟩
  filter_upwards [hQnear, hblim, hY.eventually hinva.eventually_analyticAt,
    ht.eventually P.analytic.eventually_analyticAt] with x hqx hbx hix hmx
  haveI : NeBot (𝓝[ExternalAlgebraic.upper] (x : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (Boundary.real_mem_closure_upper x)
  have hXlim : Tendsto X (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (Y x)) :=
    ((tendsto_pi_nhds.mp hbx i).sub_const (m₀ i : ℂ)).div_const d
  have hTlim : Tendsto T (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (t x)) :=
    hix.continuousAt.tendsto.comp hXlim
  have hMlim : Tendsto (fun z => P.curve (T z)) (𝓝[ExternalAlgebraic.upper] (x : ℂ))
      (𝓝 (P.curve (t x))) := hmx.continuousAt.tendsto.comp hTlim
  have hTim := Complex.continuous_im.continuousAt.tendsto.comp hTlim
  have hTre := Complex.continuous_re.continuousAt.tendsto.comp hTlim
  have henergy : Tendsto (fun z : ℂ => z - (τ : ℂ))
      (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 ((x - τ : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_sub] using
      ((tendsto_id : Tendsto (id : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ))).mono_left
        nhdsWithin_le_nhds).sub_const (τ : ℂ)
  refine ⟨tendsto_nhds_unique hbx (hMlim.congr' (hqx.mono fun _ h => h.1.symm)),
    tendsto_nhds_unique henergy
      ((tendsto_const_nhds.mul (hTlim.pow P.degree)).congr' (hqx.mono fun _ h => h.2.1.symm)),
    ge_of_tendsto hTim (hqx.mono fun _ h => h.2.2.1.le), ?_⟩
  intro hk
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (hTre.pow 2))
    (hTim.pow 2) (hqx.mono fun _ h => h.2.2.2 hk)

end NonSymmetricDyson.Full.Singularities
