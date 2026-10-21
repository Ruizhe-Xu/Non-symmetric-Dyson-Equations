import Dyson.Full.BoundaryPuiseux

/-!
# Two-point Hölder estimates from the root expansion

The sole extra analytic input in this file is the standard Hölder estimate
for a principal Nth root on a closed half-plane. It concerns the root map,
not the Dyson solution or a composed algebraic function. The composition
estimate is proved using Mathlib's local Lipschitz theorem for analytic maps.
-/

noncomputable section
open scoped Topology
open Filter Set

namespace NonSymmetricDyson.Full.Boundary

open ExternalAlgebraic

/-- Standard root estimate, universally quantified independently of any
Dyson equation or polynomial branch. -/
def RootHolderTheory : Prop :=
  ∀ (N : ℕ) (τ : ℝ) (root : ℂ → ℂ), 0 < N → root (τ : ℂ) = 0 →
    (∀ (r θ : ℝ), 0 < r → θ ∈ Icc (0 : ℝ) Real.pi →
      root (ray τ r θ) = ((r ^ (1 / (N : ℝ)) : ℝ) : ℂ) *
        Complex.exp ((((θ / (N : ℝ)) : ℝ) : ℂ) * Complex.I)) →
    ∃ H : ℝ, 0 ≤ H ∧ ∀ z ∈ closedUpper, ∀ w ∈ closedUpper,
      ‖root z - root w‖ ≤ H * ‖z - w‖ ^ (1 / (N : ℝ))

def LocalHolderOn (f : ℂ → ℂ) (D : Set ℂ) (x : ℂ) : Prop :=
  ∃ α C r : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ 0 < r ∧
    ∀ z ∈ D, ∀ w ∈ D, ‖z - x‖ < r → ‖w - x‖ < r →
      ‖f z - f w‖ ≤ C * ‖z - w‖ ^ α

theorem analyticAt_localHolder {f : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ f x)
    (D : Set ℂ) : LocalHolderOn f D x := by
  obtain ⟨K, t, ht, hLip⟩ := h.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨1, K, r, zero_lt_one, le_rfl, K.coe_nonneg, hr, ?_⟩
  intro z hz w hw hzx hwx
  have hzmem : z ∈ t := hrt (by simpa [Metric.mem_ball, dist_eq_norm] using hzx)
  have hwmem : w ∈ t := hrt (by simpa [Metric.mem_ball, dist_eq_norm] using hwx)
  simpa only [dist_eq_norm, Real.rpow_one] using hLip.dist_le_mul z hzmem w hwmem

/-- An actual convergent Puiseux chart with no negative power gives a
two-point estimate for the original function on the upper half-disk. -/
theorem PuiseuxChart.localHolder (roots : RootHolderTheory)
    {f : ℂ → ℂ} {τ : ℝ} (p : PuiseuxChart f τ) (hk : 0 ≤ p.exponent) :
    LocalHolderOn f upper (τ : ℂ) := by
  let G : ℂ → ℂ := fun t => t ^ p.exponent.toNat * p.factor t
  have hG : AnalyticAt ℂ G 0 := (analyticAt_id.pow p.exponent.toNat).mul p.factor_analytic
  obtain ⟨K, t, ht, hLip⟩ := hG.hasStrictFDerivAt.exists_lipschitzOnWith
  have hτ : (τ : ℂ) ∈ closedUpper := by simp
  have hr : Tendsto p.root (𝓝[upper] (τ : ℂ)) (𝓝 0) := by
    simpa only [p.root_center] using
      ((p.root_continuous _ hτ).mono (show upper ⊆ closedUpper from fun z hz => (show 0 < z.im from hz).le)).tendsto
  obtain ⟨r, hrpos, hrt⟩ := Metric.mem_nhdsWithin_iff.mp (hr ht)
  obtain ⟨H, hH, hroot⟩ := roots p.denominator τ p.root p.denominator_pos p.root_center p.root_ray
  have hN : (0 : ℝ) < p.denominator := by exact_mod_cast p.denominator_pos
  have hN1 : (1 : ℝ) ≤ p.denominator := by exact_mod_cast p.denominator_pos
  refine ⟨1 / p.denominator, (K : ℝ) * H, min r p.radius,
    div_pos zero_lt_one hN, ?_, mul_nonneg K.coe_nonneg hH,
    lt_min hrpos p.radius_pos, ?_⟩
  · exact (div_le_one hN).mpr hN1
  · intro z hz w hw hzx hwx
    have hzroot : p.root z ∈ t := hrt ⟨by
      simpa only [Metric.mem_ball, dist_eq_norm] using hzx.trans_le (min_le_left _ _), hz⟩
    have hwroot : p.root w ∈ t := hrt ⟨by
      simpa only [Metric.mem_ball, dist_eq_norm] using hwx.trans_le (min_le_left _ _), hw⟩
    have hexp (v : ℂ) (hv : v ∈ upper) (hvx : ‖v - (τ : ℂ)‖ < min r p.radius) :
        f v = G (p.root v) := by
      rw [p.expansion v hv (hvx.trans_le (min_le_right _ _))]
      dsimp [G]
      rw [show p.root v ^ p.exponent = p.root v ^ p.exponent.toNat by
        simpa only [Int.toNat_of_nonneg hk] using zpow_natCast (p.root v) p.exponent.toNat]
    rw [hexp z hz hzx, hexp w hw hwx]
    calc
      ‖G (p.root z) - G (p.root w)‖ ≤ (K : ℝ) * ‖p.root z - p.root w‖ := by
        simpa only [dist_eq_norm] using hLip.dist_le_mul _ hzroot _ hwroot
      _ ≤ (K : ℝ) * (H * ‖z - w‖ ^ (1 / (p.denominator : ℝ))) :=
        mul_le_mul_of_nonneg_left (hroot z (show 0 ≤ z.im from (show 0 < z.im from hz).le) w
          (show 0 ≤ w.im from (show 0 < w.im from hw).le)) K.coe_nonneg
      _ = _ := by ring

/-- Boundedness of the original function on a vertical line removes the
negative-power alternative and therefore gives the local two-point estimate. -/
theorem algebraic_localHolder_of_bounded
    (puiseux : ConvergentPuiseuxTheory) (roots : RootHolderTheory)
    (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f upper) (halg : AlgebraicOnUpper f)
    (hPick : ∀ z ∈ upper, 0 < (f z).im) (τ M : ℝ)
    (hbound : ∀ η : ℝ, 0 < η → ‖f (vertical τ η)‖ ≤ M) :
    LocalHolderOn f upper (τ : ℂ) := by
  have hI : Complex.I ∈ upper := by simp
  have hnonzero : f Complex.I ≠ 0 := by
    intro hz
    have hp := hPick _ hI
    simpa [hz] using hp
  obtain ⟨_, hcharts⟩ := puiseux f ha halg ⟨Complex.I, hI, hnonzero⟩
  obtain ⟨p⟩ := hcharts τ
  have hk : 0 ≤ p.exponent := by
    by_contra hk
    exact not_singular_of_bounded hbound (norm_diverges_of_imaginary
      (PuiseuxChart.imaginary_diverges p (fun z hz => (hPick z hz).le) (lt_of_not_ge hk)))
  exact PuiseuxChart.localHolder roots p hk

end NonSymmetricDyson.Full.Boundary
