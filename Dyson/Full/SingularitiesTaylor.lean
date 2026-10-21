import Dyson.Full.SingularitiesPhysical

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.Singularities

/-- The second-order analytic remainder is obtained directly from Mathlib's
convergent power-series estimate, with the supplied first derivative. -/
theorem analytic_quadratic_taylor_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (d : E) (ha : AnalyticAt ℂ f 0) (hd : HasDerivAt f d 0) :
    ∃ C > 0, ∀ᶠ s in 𝓝 (0 : ℂ), ‖f s - f 0 - s • d‖ ≤ C * ‖s‖ ^ 2 := by
  obtain ⟨p, hp⟩ := ha
  have hd' : p 1 (fun _ => 1) = d := hp.hasDerivAt.unique hd
  have hfirst (s : ℂ) : p 1 (fun _ => s) = s • d := by
    have hh := (p 1).map_smul_univ (fun _ => s) (fun _ => (1 : ℂ))
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, pow_one, hd'] using hh
  have hpartial (s : ℂ) : p.partialSum 2 s = f 0 + s • d := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hp.coeff_zero, hfirst]
  obtain ⟨C, hC, hb⟩ := (hp.isBigO_sub_partialSum_pow 2).exists_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb.bound] with s hs
  simpa only [zero_add, hpartial, sub_add_eq_sub_sub, norm_pow,
    Real.norm_eq_abs, abs_norm] using hs

variable {ι : Type*} [Fintype ι]

/-- The analytic physical vector in the exact monomial coordinate has the
positive Perron tangent and a genuine uniform quadratic error. -/
theorem physical_curve_taylor_bound
    (curve : ℂ → ℂ × (ι → ℂ)) (χ : ℂ → ℂ) (m₀ q r : ι → ℝ)
    (hca : AnalyticAt ℂ curve 0) (hc0 : curve 0 = 0)
    (hcd : HasDerivAt curve (0, fun i => (r i : ℂ)) 0)
    (hχa : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) (hχd : HasDerivAt χ 1 0) :
    ∃ C > 0, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ i,
      ‖((m₀ i : ℂ) + (q i : ℂ) * (curve (χ s)).2 i) - (m₀ i : ℂ) -
        (q i * r i : ℝ) * s‖ ≤ C * ‖s‖ ^ 2 := by
  let M : ℂ → ι → ℂ := fun s i => (m₀ i : ℂ) + (q i : ℂ) * (curve (χ s)).2 i
  have hMa : AnalyticAt ℂ M 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact analyticAt_const.add (analyticAt_const.mul
      ((((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)).analyticAt _).comp
        (((ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)).analyticAt _).comp
          (hca.comp_of_eq hχa hχ0))))
  have hMd : HasDerivAt M (fun i => (q i * r i : ℝ)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    let ev : (ℂ × (ι → ℂ)) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))
    have hh := ev.hasFDerivAt.comp_hasDerivAt 0 (hcd.scomp_of_eq 0 hχd hχ0.symm)
    convert (hasDerivAt_const 0 (m₀ i : ℂ)).add
      ((hasDerivAt_const 0 (q i : ℂ)).mul hh) using 1 <;> simp [ev]
  obtain ⟨C, hC, hb⟩ := analytic_quadratic_taylor_bound M (fun i => (q i * r i : ℝ)) hMa hMd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with s hs i
  have hh := (norm_le_pi_norm (M s - M 0 - s • (fun i => ((q i * r i : ℝ) : ℂ)))) i
  simpa only [M, hc0, hχ0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Prod.snd_zero, Pi.zero_apply, mul_zero, add_zero, sub_self, mul_comm] using hh.trans hs

end NonSymmetricDyson.Full.Singularities
