import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Arithmetic gluing of the rough and fine nonlinear stability regimes.
The proof includes E=0 and explicitly separates the degenerate E=d=0 case.
No external result or assumed unified conclusion occurs here. -/
noncomputable section
namespace NonSymmetricDyson.Full.PowerGluing

/-- The constant is independent of the forcing size E and background scale d. -/
def gluingConstant (A B c p : ℝ) : ℝ :=
  max (A*(1+c⁻¹)) (B*(1+c)^(1-p))

theorem power_div_identity {q p : ℝ} (hq : 0 < q) :
    q^p = q/q^(1-p) := by
  calc
    q^p = q^(1-(1-p)) := by congr 1; ring
    _ = q^1/q^(1-p) := Real.rpow_sub hq _ _
    _ = q/q^(1-p) := by rw [Real.rpow_one]

/-- The rough root bound becomes the unified quotient when forcing dominates
background distance. The statement also covers E=d=0. -/
theorem rough_to_unified {E d c p A R : ℝ}
    (hE : 0 ≤ E) (hd : 0 ≤ d) (hc : 0 < c) (hp : 0 < p) (hA : 0 ≤ A)
    (hregime : c*d ≤ E) (hrough : R ≤ A*(E+d)^p) :
    R ≤ (A*(1+c⁻¹)) * (E/(E+d)^(1-p)) := by
  by_cases hq : E+d = 0
  · have hE0 : E = 0 := by linarith
    have hd0 : d = 0 := by linarith
    simpa [hE0, hd0, Real.zero_rpow hp.ne'] using hrough
  have hqpos : 0 < E+d := lt_of_le_of_ne (add_nonneg hE hd) (Ne.symm hq)
  have hdE : d ≤ E/c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hsum : E+d ≤ (1+c⁻¹)*E := by
    rw [div_eq_mul_inv] at hdE
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left hsum hA
  have hdiv := div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hqpos.le (1-p))
  rw [power_div_identity hqpos] at hrough
  calc
    R ≤ A*((E+d)/(E+d)^(1-p)) := hrough
    _ ≤ (A*(1+c⁻¹)) * (E/(E+d)^(1-p)) := by
      convert hdiv using 1 <;> ring

/-- The fine linear-response bound is uniform after replacing the background
scale d by the combined scale E+d. -/
theorem fine_to_unified {E d c p B R : ℝ}
    (hE : 0 ≤ E) (hd : 0 < d) (hc : 0 < c) (hp1 : p ≤ 1) (hB : 0 ≤ B)
    (hregime : E ≤ c*d) (hfine : R ≤ B*E/d^(1-p)) :
    R ≤ (B*(1+c)^(1-p)) * (E/(E+d)^(1-p)) := by
  have hq : 0 < E+d := add_pos_of_nonneg_of_pos hE hd
  have hK : 0 < 1+c := by positivity
  have hden : (E+d)^(1-p) ≤ (1+c)^(1-p)*d^(1-p) := by
    have h := Real.rpow_le_rpow hq.le (show E+d ≤ (1+c)*d by nlinarith)
      (show 0 ≤ 1-p by linarith)
    rwa [Real.mul_rpow hK.le hd.le] at h
  have hprod := mul_le_mul_of_nonneg_left hden (mul_nonneg hB hE)
  apply hfine.trans
  have hdpos := Real.rpow_pos_of_pos hd (1-p)
  have hqpos := Real.rpow_pos_of_pos hq (1-p)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hdpos hqpos).mpr
  nlinarith

/-- The closed rough regime handles the degenerate case E=d=0 automatically.
This version needs no separate vanishing hypothesis at zero. -/
theorem two_regime_gluing {E d c p A B R : ℝ}
    (hE : 0 ≤ E) (hd : 0 ≤ d) (hc : 0 < c) (hp : 0 < p) (hp1 : p < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrough : c*d ≤ E → R ≤ A*(E+d)^p)
    (hfine : E ≤ c*d → 0 < d → R ≤ B*E/d^(1-p)) :
    R ≤ gluingConstant A B c p * (E/(E+d)^(1-p)) := by
  have hn : 0 ≤ E/(E+d)^(1-p) := div_nonneg hE (Real.rpow_nonneg (add_nonneg hE hd) _)
  by_cases hregime : c*d ≤ E
  · exact (rough_to_unified hE hd hc hp hA hregime (hrough hregime)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
  · have hdpos : 0 < d := by
      by_contra hh
      have hdz : d = 0 := le_antisymm (le_of_not_gt hh) hd
      simp [hdz, hE] at hregime
    have hregime' : E ≤ c*d := le_of_lt (lt_of_not_ge hregime)
    exact (fine_to_unified hE hdpos hc hp1.le hB hregime' (hfine hregime' hdpos)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)

/-- The strict rough/closed fine split used in the nonlinear argument.
Positive d includes the whole upper half-plane and E=0 is allowed. -/
theorem two_regime_gluing_positive_background {E d c p A B R : ℝ}
    (hE : 0 ≤ E) (hd : 0 < d) (hc : 0 < c) (hp : 0 < p) (hp1 : p < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrough : c*d < E → R ≤ A*(E+d)^p)
    (hfine : E ≤ c*d → R ≤ B*E/d^(1-p)) :
    R ≤ gluingConstant A B c p * (E/(E+d)^(1-p)) := by
  have hn : 0 ≤ E/(E+d)^(1-p) := div_nonneg hE (Real.rpow_nonneg (by positivity) _)
  by_cases hregime : E ≤ c*d
  · exact (fine_to_unified hE hd hc hp1.le hB hregime (hfine hregime)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)
  · have hr : c*d < E := lt_of_not_ge hregime
    exact (rough_to_unified hE hd.le hc hp hA hr.le (hrough hr)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)

/-- Degenerate d=0 is also covered with strict rough hypotheses, provided the
unforced solution is exactly reconstructed at E=d=0. -/
theorem two_regime_gluing_nonnegative_background {E d c p A B R : ℝ}
    (hE : 0 ≤ E) (hd : 0 ≤ d) (hc : 0 < c) (hp : 0 < p) (hp1 : p < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : E+d = 0 → R ≤ 0)
    (hrough : c*d < E → R ≤ A*(E+d)^p)
    (hfine : E ≤ c*d → 0 < d → R ≤ B*E/d^(1-p)) :
    R ≤ gluingConstant A B c p * (E/(E+d)^(1-p)) := by
  by_cases hdpos : 0 < d
  · exact two_regime_gluing_positive_background hE hdpos hc hp hp1 hA hB hrough
      (fun h => hfine h hdpos)
  have hd0 : d = 0 := le_antisymm (le_of_not_gt hdpos) hd
  by_cases hE0 : E = 0
  · have hh := hzero (by simp [hE0, hd0])
    simpa [hE0, hd0] using hh
  have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
  have hr : c*d < E := by simpa [hd0] using hEpos
  have hn : 0 ≤ E/(E+d)^(1-p) := div_nonneg hE (Real.rpow_nonneg (add_nonneg hE hd) _)
  exact (rough_to_unified hE hd hc hp hA hr.le (hrough hr)).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)

theorem gluingConstant_pos {A B c p : ℝ} (hA : 0 < A) (hc : 0 < c) :
    0 < gluingConstant A B c p := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  exact mul_pos hA (by positivity)

/-- The radius denominator in the anchored root argument has exactly the
fractional power used by the fine regime, for every integer k>0. -/
theorem root_power_identity (d : ℝ) (hd : 0 ≤ d) (k : ℕ) (hk : 0 < k) :
    (d^(1/(k:ℝ)))^(k-1) = d^(1-1/(k:ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk)), Nat.cast_one]
  field_simp
  <;> ring

/-- The exact fine-radius coefficient, extracting the root-separation and
leading-coefficient factors without hiding them in asymptotic notation. -/
theorem fine_radius_identity {E d croot csep : ℝ} (hd : 0 ≤ d)
    (k : ℕ) (hk : 0 < k) :
    E/(croot*(csep*d^(1/(k:ℝ))/2)^(k-1)) =
      ((2:ℝ)^(k-1)/(croot*csep^(k-1))) * E/d^(1-1/(k:ℝ)) := by
  rw [div_pow, mul_pow, root_power_identity d hd k hk]
  field_simp
  <;> ring

/-- A genuine polynomial bound on a nonnegative norm gives its fractional
root bound, with the coefficient extracted exactly. -/
theorem nonnegative_power_bound_to_root {H C X : ℝ} (hH : 0 ≤ H)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (k : ℕ) (hk : 0 < k)
    (hbound : H^k ≤ C*X) : H ≤ C^(1/(k:ℝ))*X^(1/(k:ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkk : (k:ℝ)*(1/(k:ℝ)) = 1 := by field_simp
  have hroot := Real.rpow_le_rpow (pow_nonneg hH k) hbound
    (show 0 ≤ 1/(k:ℝ) by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hH, hkk, Real.rpow_one,
    Real.mul_rpow hC hX] at hroot
  exact hroot

end NonSymmetricDyson.Full.PowerGluing
