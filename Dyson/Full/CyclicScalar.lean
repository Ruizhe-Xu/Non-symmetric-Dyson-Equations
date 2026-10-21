import Dyson.Full.CyclicExample

/-! The scalar semicircle branch at every interior energy, and the exact
root of unity used by the general directed-cycle example. -/

noncomputable section
open scoped Topology
open Filter
namespace NonSymmetricDyson.Full.CyclicExample

theorem unit_upper_normSq (w : ℂ) (hw : ‖w‖ = 1) : w.re ^ 2 + w.im ^ 2 = 1 := by
  have h := Complex.normSq_eq_norm_sq w
  simpa [Complex.normSq_apply, hw, pow_two] using h

theorem unit_upper_energy (w : ℂ) (hw : ‖w‖ = 1) (hi : 0 < w.im) :
    -2 < -2*w.re ∧ -2*w.re < 2 := by
  have hh := unit_upper_normSq w hw
  have hre := Complex.abs_re_le_norm w
  rw [hw] at hre
  have hre' := abs_le.mp hre
  constructor <;> nlinarith [sq_pos_of_pos hi]

theorem root_at_unit_energy (w : ℂ) (hw : ‖w‖ = 1) (hi : 0 < w.im) :
    root ((-2*w.re : ℝ) : ℂ) = (2*w.im : ℂ) := by
  have hsq : (2*w.im : ℂ)^2 = 4 - (((-2*w.re : ℝ) : ℂ))^2 := by
    have hh := unit_upper_normSq w hw
    push_cast
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> nlinarith
  have h := Complex.sq_cpow_two_inv (x := (2*w.im : ℂ)) (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hi))
  rw [hsq] at h
  exact h

theorem scalar_at_unit_energy (w : ℂ) (hw : ‖w‖ = 1) (hi : 0 < w.im) :
    scalar ((-2*w.re : ℝ) : ℂ) = w := by
  rw [scalar, root_at_unit_energy w hw hi]
  apply Complex.ext <;> simp <;> ring

theorem scalar_differentiable_at_energy (τ : ℝ) (hτ : -2 < τ ∧ τ < 2) :
    DifferentiableAt ℂ scalar (τ : ℂ) := by
  have hr : DifferentiableAt ℂ root (τ : ℂ) := by
    apply DifferentiableAt.cpow_const
      (differentiableAt_const 4 |>.sub (differentiableAt_id.pow 2))
    rw [Complex.mem_slitPlane_iff]
    left
    simp [pow_two, Complex.mul_re]
    nlinarith
  exact ((differentiableAt_id.neg).add (hr.const_mul Complex.I)).div_const 2

theorem scalar_hasDerivAt_unit_energy (w : ℂ) (hw : ‖w‖ = 1) (hi : 0 < w.im) :
    HasDerivAt scalar (-w / ((2*w.im : ℂ)*Complex.I)) ((-2*w.re : ℝ) : ℂ) := by
  let τ : ℂ := ((-2*w.re : ℝ) : ℂ)
  have hd := scalar_differentiable_at_energy (-2*w.re) (unit_upper_energy w hw hi)
  have hp := ((hd.hasDerivAt.pow 2).add ((hasDerivAt_id τ).mul hd.hasDerivAt)).add_const 1
  have hzfun : (fun z : ℂ => scalar z^2 + z*scalar z + 1) = fun _ => 0 := funext scalar_quadratic
  change HasDerivAt (fun z : ℂ => scalar z^2+z*scalar z+1) _ τ at hp
  rw [hzfun] at hp
  have he := hp.unique (hasDerivAt_const τ (0 : ℂ))
  have hs : scalar τ = w := scalar_at_unit_energy w hw hi
  simp only [Nat.cast_ofNat, show 2 - 1 = 1 by decide, pow_one, one_mul, id_eq] at he
  change 2 * scalar τ * deriv scalar τ + (scalar τ + τ * deriv scalar τ) = 0 at he
  rw [hs] at he
  have hcoef : 2*w+τ = (2*w.im : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [τ] <;> ring
  have hn : (2*w.im : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (mul_pos (by norm_num : (0:ℝ)<2) hi).ne') Complex.I_ne_zero
  have hderiv : deriv scalar τ = -w / ((2*w.im : ℂ)*Complex.I) := by
    apply (eq_div_iff hn).mpr
    rw [← hcoef]
    linear_combination he
  change HasDerivAt scalar (-w / ((2*w.im : ℂ)*Complex.I)) τ
  rw [← hderiv]
  exact hd.hasDerivAt

theorem scalar_upper_at_energy (τ : ℝ) (hτ : -2 < τ ∧ τ < 2) :
    (scalar (τ : ℂ)).im = Real.sqrt (4-τ^2)/2 := by
  have hpos : 0 < 4-τ^2 := by nlinarith
  have hs : ((Real.sqrt (4-τ^2) : ℂ))^2 = 4-(τ:ℂ)^2 := by
    exact_mod_cast Real.sq_sqrt hpos.le
  have hh := Complex.sq_cpow_two_inv (x := (Real.sqrt (4-τ^2) : ℂ))
    (by simpa using Real.sqrt_pos.mpr hpos)
  rw [hs] at hh
  have hr : root (τ : ℂ) = (Real.sqrt (4-τ^2) : ℂ) := hh
  simp [scalar, hr]

def cyclicOmega (d : ℕ) : ℂ := Complex.exp (((2*Real.pi/(d:ℝ) : ℝ) : ℂ)*Complex.I)

theorem cyclicOmega_norm (d : ℕ) : ‖cyclicOmega d‖ = 1 := by
  simp [cyclicOmega, Complex.norm_exp]

theorem cyclicOmega_im (d : ℕ) : (cyclicOmega d).im = Real.sin (2*Real.pi/(d:ℝ)) := by
  exact Complex.exp_ofReal_mul_I_im _

theorem cyclicOmega_re (d : ℕ) : (cyclicOmega d).re = Real.cos (2*Real.pi/(d:ℝ)) := by
  exact Complex.exp_ofReal_mul_I_re _

theorem cyclicOmega_upper (d : ℕ) (hd : 3 ≤ d) : 0 < (cyclicOmega d).im := by
  have hd' : (2:ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  rw [cyclicOmega_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · apply (div_lt_iff₀ (by linarith : (0:ℝ)<d)).mpr
    nlinarith [Real.pi_pos]

theorem cyclicOmega_pow (d : ℕ) (hd : 0 < d) : cyclicOmega d ^ d = 1 := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [cyclicOmega, ← Complex.exp_nat_mul]
  have he : (d:ℂ)*((((2*Real.pi/(d:ℝ) : ℝ) : ℂ))*Complex.I) =
      2*Real.pi*Complex.I := by push_cast; field_simp
  rw [he, Complex.exp_two_pi_mul_I]

end NonSymmetricDyson.Full.CyclicExample
