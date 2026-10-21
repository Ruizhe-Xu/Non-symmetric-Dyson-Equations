import Dyson.Full.NonlinearPath
import Dyson.Full.PowerGluing

noncomputable section
open scoped Topology
open Filter

namespace NonSymmetricDyson.Full.Nonlinear

theorem rootDenominator_product (c : ℝ) (k : ℕ) (hk : 0 < k) (ω : ℂ) :
    (c*‖ω‖^((1:ℝ)/k))*rootDenominator c k ω =
      (c^(k+1)/(2:ℝ)^(k-1))*‖ω‖ := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hroot : (‖ω‖^((1:ℝ)/k))^k = ‖ω‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have he : (1/(k:ℝ))*(k:ℝ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hprod (x : ℝ) : x*x^(k-1) = x^k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  calc
    _ = c*((c*‖ω‖^((1:ℝ)/k))*(c*‖ω‖^((1:ℝ)/k))^(k-1))/(2:ℝ)^(k-1) := by
      dsimp [rootDenominator]
      rw [div_pow]
      ring
    _ = c*(c*‖ω‖^((1:ℝ)/k))^k/(2:ℝ)^(k-1) := by rw [hprod]
    _ = _ := by rw [mul_pow, hroot, pow_succ]; ring

theorem rootDenominator_gap (c A E d : ℝ) (hc : 0 < c) (hA : 0 < A)
    (hd : 0 < d) (k : ℕ) (hk : 0 < k) (ω : ℂ)
    (hdω : d ≤ ‖ω‖)
    (hE : E ≤ ((c^(k+1)/(2:ℝ)^(k-1))/(4*A))*d) :
    2*(A*E) < (c*‖ω‖^((1:ℝ)/k))*rootDenominator c k ω := by
  rw [rootDenominator_product c k hk]
  let B := c^(k+1)/(2:ℝ)^(k-1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hh := mul_le_mul_of_nonneg_left hE (show 0 ≤ 2*A by positivity)
  have he : (2*A)*((B/(4*A))*d) = B*d/2 := by field_simp; ring
  change 2*A*E ≤ (2*A)*((B/(4*A))*d) at hh
  rw [he] at hh
  have hbd := mul_le_mul_of_nonneg_left hdω hB.le
  change 2*(A*E) < B*‖ω‖
  nlinarith [mul_pos hB hd]

theorem rootDenominator_small (c : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ω : ℂ, ‖ω‖ < δ → rootDenominator c k ω ≤ 1 := by
  have hkpos : 0 < k := by omega
  have hp : 0 < (1:ℝ)/k := by positivity
  have hr : Continuous (fun ω : ℂ => ‖ω‖^((1:ℝ)/k)) :=
    continuous_norm.rpow_const (fun _ => Or.inr hp.le)
  have hf : Continuous (rootDenominator c k) := by
    exact continuous_const.mul (((continuous_const.mul hr).div_const 2).pow (k-1))
  have hz : rootDenominator c k 0 = 0 := by
    dsimp [rootDenominator]
    rw [norm_zero, Real.zero_rpow hp.ne']
    simp [Nat.sub_ne_zero_of_lt (show 1 < k by omega)]
  have hev : ∀ᶠ ω in 𝓝 (0 : ℂ), rootDenominator c k ω ≤ 1 :=
    hf.continuousAt.tendsto.eventually_le_const (by rw [hz]; norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨δ,hδ,fun ω hω => hball (by simpa using hω)⟩

end NonSymmetricDyson.Full.Nonlinear
