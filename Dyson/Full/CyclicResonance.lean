import Dyson.Full.CyclicGeneralLimit

/-! Exact finite resonance set for the directed-cycle stability matrix. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.CyclicGeneral

variable (d : ℕ) [NeZero d]

def resonantPhase (k : ℤ) : ℂ :=
  Complex.exp ((((k : ℝ)*Real.pi/(d : ℝ) : ℝ) : ℂ)*Complex.I)

@[simp] theorem resonantPhase_norm (k : ℤ) : ‖resonantPhase d k‖=1 := by
  simp [resonantPhase, Complex.norm_exp]

@[simp] theorem resonantPhase_re (k : ℤ) :
    (resonantPhase d k).re=Real.cos ((k : ℝ)*Real.pi/(d : ℝ)) :=
  Complex.exp_ofReal_mul_I_re _

@[simp] theorem resonantPhase_im (k : ℤ) :
    (resonantPhase d k).im=Real.sin ((k : ℝ)*Real.pi/(d : ℝ)) :=
  Complex.exp_ofReal_mul_I_im _

theorem resonantPhase_upper (k : ℤ) (hk : 0<k) (hkd : k<(d : ℤ)) :
    0<(resonantPhase d k).im := by
  have hd : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
  have hk' : (0 : ℝ)<k := by exact_mod_cast hk
  have hkd' : (k : ℝ)<d := by exact_mod_cast hkd
  rw [resonantPhase_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]

theorem resonantPhase_pow (k : ℤ) : resonantPhase d k^(2*d)=1 := by
  have hd : (d : ℂ)≠0 := by exact_mod_cast NeZero.ne d
  rw [resonantPhase, ← Complex.exp_nat_mul]
  have he : ((2*d : ℕ) : ℂ)*((((k : ℝ)*Real.pi/(d : ℝ) : ℝ) : ℂ)*Complex.I)=
      (k : ℂ)*(2*Real.pi*Complex.I) := by push_cast; field_simp
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem resonant_unit_iff (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    w^(2*d)=1 ↔ ∃ k : ℤ, 0<k ∧ k<(d : ℤ) ∧ w=resonantPhase d k := by
  constructor
  · intro hwd
    have he : Complex.exp ((w.arg : ℂ)*Complex.I)=w := by
      simpa [hw] using Complex.norm_mul_exp_arg_mul_I w
    rw [← he, ← Complex.exp_nat_mul] at hwd
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp hwd
    have him := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im, zero_mul, mul_zero, mul_one,
      add_zero, Nat.cast_mul, Nat.cast_ofNat] at him
    norm_num [Complex.mul_re, Complex.mul_im] at him
    have ha : 0<w.arg := by
      have hnonneg := Complex.arg_nonneg_iff.mpr hi.le
      have hne : w.arg≠0 := by
        intro hh
        exact hi.ne' (Complex.arg_eq_zero_iff.mp hh).2
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hapi : w.arg<Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')
    have hd : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
    have hkpos : (0 : ℝ)<k := by nlinarith [Real.pi_pos, mul_pos hd ha]
    have hklt : (k : ℝ)<d := by nlinarith [Real.pi_pos, mul_pos hd (sub_pos.mpr hapi)]
    have harg : w.arg=(k : ℝ)*Real.pi/(d : ℝ) := by
      apply (eq_div_iff hd.ne').mpr
      nlinarith [him]
    refine ⟨k, by exact_mod_cast hkpos, by exact_mod_cast hklt, ?_⟩
    rw [resonantPhase, ← harg]
    exact he.symm
  · rintro ⟨k,hk,hkd,rfl⟩
    exact resonantPhase_pow d k

/-- The full resonant boundary set in its exact finite phase parametrization. -/
theorem boundary_resonance_iff (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    (∃ v : Space d, v≠0 ∧ (1-w^2 • shift₂ d) v=0) ↔
      ∃ k : ℤ, 0<k ∧ k<(d : ℤ) ∧ w=resonantPhase d k := by
  rw [resonance_iff, ← pow_mul, resonant_unit_iff d w hw hi]

theorem scalar_boundary_unit (τ : ℝ) (hτ : -2<τ ∧ τ<2) :
    ‖CyclicExample.scalar (τ : ℂ)‖=1 ∧
    0<(CyclicExample.scalar (τ : ℂ)).im ∧
    -2*(CyclicExample.scalar (τ : ℂ)).re=τ := by
  let b := CyclicExample.scalar (τ : ℂ)
  have hi : 0<b.im := by
    rw [CyclicExample.scalar_upper_at_energy τ hτ]
    exact div_pos (Real.sqrt_pos.mpr (by nlinarith)) (by norm_num)
  have he := CyclicExample.scalar_quadratic (τ : ℂ)
  have hr := congrArg Complex.re he
  have hm := congrArg Complex.im he
  change (b^2+(τ : ℂ)*b+1).re=0 at hr
  change (b^2+(τ : ℂ)*b+1).im=0 at hm
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hm
  have hx : 2*b.re+τ=0 := by
    have hh : b.im*(2*b.re+τ)=0 := by nlinarith [hm]
    exact (mul_eq_zero.mp hh).resolve_left hi.ne'
  have hn := Complex.normSq_eq_norm_sq b
  simp only [Complex.normSq_apply] at hn
  have hnorm : ‖b‖=1 := by nlinarith [norm_nonneg b]
  exact ⟨hnorm,hi,by linarith⟩

/-- In real energy coordinates the singular set is exactly the finite set
`{-2*cos(k*pi/d) | 0<k<d}`. -/
theorem resonant_energy_iff (τ : ℝ) (hτ : -2<τ ∧ τ<2) :
    (∃ v : Space d, v≠0 ∧ (1-(CyclicExample.scalar (τ : ℂ))^2 • shift₂ d) v=0) ↔
      ∃ k : ℤ, 0<k ∧ k<(d : ℤ) ∧ τ= -2*Real.cos ((k : ℝ)*Real.pi/(d : ℝ)) := by
  obtain ⟨hw,hi,he⟩ := scalar_boundary_unit τ hτ
  rw [boundary_resonance_iff d _ hw hi]
  constructor
  · rintro ⟨k,hk,hkd,hphase⟩
    refine ⟨k,hk,hkd,?_⟩
    rw [hphase, resonantPhase_re] at he
    exact he.symm
  · rintro ⟨k,hk,hkd,hτk⟩
    refine ⟨k,hk,hkd,?_⟩
    have hs := CyclicExample.scalar_at_unit_energy (resonantPhase d k)
      (resonantPhase_norm d k) (resonantPhase_upper d k hk hkd)
    rw [resonantPhase_re, ← hτk] at hs
    exact hs

/-- Each and every interior resonance has the sharp constant `sin(kπ/d)`. -/
theorem all_resonant_energy_limits (k : ℤ) (hk : 0<k) (hkd : k<(d : ℤ)) :
    Tendsto (fun η : ℝ => if hη : 0<η then
      η*canonicalInverseNorm d (heightPoint (-2*Real.cos ((k : ℝ)*Real.pi/(d : ℝ))) η)
        (by simpa using hη) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin ((k : ℝ)*Real.pi/(d : ℝ)))) := by
  simpa only [resonantPhase_re, resonantPhase_im] using
    canonical_inverse_exact_limit d (resonantPhase d k) (resonantPhase_norm d k)
      (resonantPhase_upper d k hk hkd) (resonantPhase_pow d k)

end NonSymmetricDyson.Full.CyclicGeneral
