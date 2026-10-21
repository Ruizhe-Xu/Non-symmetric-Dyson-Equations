import Dyson.Full.CyclicGeneralInverse

/-! Sharp instability at every resonant interior energy of a directed cycle. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set Fin.NatCast

namespace NonSymmetricDyson.Full.CyclicGeneral

variable (d : ℕ) [NeZero d]
open CyclicExample (scalar)

def heightPoint (τ η : ℝ) : ℂ := (τ : ℂ)+(η : ℂ)*Complex.I

@[simp] theorem heightPoint_im (τ η : ℝ) : (heightPoint τ η).im=η := by
  simp [heightPoint]

theorem heightPoint_distance (τ η : ℝ) (hη : 0 ≤ η) :
    ‖heightPoint τ η-(τ : ℂ)‖=η := by
  simp [heightPoint, norm_mul, Complex.norm_real, abs_of_nonneg hη]

theorem heightPoint_tendsto (τ : ℝ) :
    Tendsto (heightPoint τ) (𝓝[>] (0 : ℝ)) (𝓝 (τ : ℂ)) := by
  have h : Continuous (heightPoint τ) := by unfold heightPoint; fun_prop
  simpa [heightPoint] using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

def denominator (z : ℂ) : ℂ := 1-(scalar z^2)^d

theorem denominator_zero (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im)
    (hwd : w^(2*d)=1) : denominator d ((-2*w.re : ℝ) : ℂ)=0 := by
  rw [denominator, CyclicExample.scalar_at_unit_energy w hw hi, ← pow_mul, hwd, sub_self]

theorem denominator_hasDerivAt (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im)
    (hwd : w^(2*d)=1) :
    HasDerivAt (denominator d) ((d : ℂ)/((w.im : ℂ)*Complex.I))
      ((-2*w.re : ℝ) : ℂ) := by
  have hd := (hasDerivAt_const ((-2*w.re : ℝ) : ℂ) (1 : ℂ)).sub
    ((CyclicExample.scalar_hasDerivAt_unit_energy w hw hi).pow (2*d))
  have hwprod : w^(2*d-1)*w=1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by have := NeZero.pos d; omega), hwd]
  have hh : (w.im : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hi.ne') Complex.I_ne_zero
  convert hd using 1
  · funext z
    simp [denominator, pow_mul]
  · rw [CyclicExample.scalar_at_unit_energy w hw hi]
    calc
      (d : ℂ)/((w.im : ℂ)*Complex.I) =
          ((d : ℂ)/((w.im : ℂ)*Complex.I))*(w^(2*d-1)*w) := by rw [hwprod, mul_one]
      _ = _ := by push_cast; field_simp; ring

theorem denominator_height_limit (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im)
    (hwd : w^(2*d)=1) :
    Tendsto (fun η : ℝ => ‖denominator d (heightPoint (-2*w.re) η)‖/η)
      (𝓝[>] (0 : ℝ)) (𝓝 ((d : ℝ)/w.im)) := by
  have hp : Tendsto (heightPoint (-2*w.re)) (𝓝[>] (0 : ℝ))
      (𝓝[≠] (((-2*w.re : ℝ) : ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨heightPoint_tendsto _, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    change heightPoint (-2*w.re) η ≠ ((-2*w.re : ℝ) : ℂ)
    intro he
    have hh := congrArg Complex.im he
    simpa using (ne_of_gt hη) (by simpa using hh)
  have hs := (hasDerivAt_iff_tendsto_slope.mp (denominator_hasDerivAt d w hw hi hwd)).comp hp
  have hn : ‖(d : ℂ)/((w.im : ℂ)*Complex.I)‖=(d : ℝ)/w.im := by
    simp [norm_div, norm_mul, Complex.norm_real, abs_of_pos hi]
  have ht := hs.norm
  rw [hn] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  simp only [Function.comp_apply, slope, denominator_zero d w hw hi hwd,
    vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv, heightPoint_distance _ _ hη.le]
  ring

theorem scalar_upper_near (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    ∀ᶠ z in 𝓝 (((-2*w.re : ℝ) : ℂ)), 0 < (scalar z).im := by
  have hc := Complex.continuous_im.continuousAt.comp
    (CyclicExample.scalar_hasDerivAt_unit_energy w hw hi).continuousAt
  apply hc.eventually
  exact lt_mem_nhds (by simpa only [Function.comp_apply,
    CyclicExample.scalar_at_unit_energy w hw hi] using hi)

/-- The actual canonical solution has the claimed resonant bulk boundary value. -/
theorem canonical_boundary_limit (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im) :
    Tendsto (fun η : ℝ => GlobalWellPosedness.solution (cycle d) (fun _ => 0)
      (cycle_nonnegative d) (heightPoint (-2*w.re) η))
      (𝓝[>] (0 : ℝ)) (𝓝 (fun _ : Fin d => w)) := by
  have hs := (CyclicExample.scalar_hasDerivAt_unit_energy w hw hi).continuousAt.tendsto.comp
    (heightPoint_tendsto (-2*w.re))
  rw [CyclicExample.scalar_at_unit_energy w hw hi] at hs
  have ht := tendsto_pi_nhds.mpr (fun _ : Fin d => hs)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (heightPoint_tendsto (-2*w.re)).eventually (scalar_upper_near w hw hi)] with η hη hm
  exact (canonical_eq_scalar d (by simpa using hη) hm).symm

/-- Exact unnormalized Euclidean inverse constant at every resonant unit
upper-half-plane boundary value.  The hypotheses are algebraic conditions on
an explicit number, not a spectral or Dyson assumption. -/
theorem canonical_inverse_exact_limit (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im)
    (hwd : w^(2*d)=1) :
    Tendsto (fun η : ℝ => if hη : 0<η then
      η*canonicalInverseNorm d (heightPoint (-2*w.re) η) (by simpa using hη) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 w.im) := by
  have hc := (numerator_continuous d).continuousAt.comp
    ((CyclicExample.scalar_hasDerivAt_unit_energy w hw hi).continuousAt.pow 2)
  have hn := hc.norm.tendsto.comp (heightPoint_tendsto (-2*w.re))
  simp only [Function.comp_apply] at hn
  rw [CyclicExample.scalar_at_unit_energy w hw hi,
    numerator_norm d (w^2) (by simp [hw]) (by simpa [← pow_mul] using hwd)] at hn
  have hdpos : (0 : ℝ)<d := by exact_mod_cast NeZero.pos d
  have ht := hn.div (denominator_height_limit d w hw hi hwd) (div_pos hdpos hi).ne'
  have hquot : (d : ℝ)/((d : ℝ)/w.im)=w.im := by field_simp
  rw [hquot] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (heightPoint_tendsto (-2*w.re)).eventually (scalar_upper_near w hw hi)] with η hη hm
  change 0<η at hη
  dsimp only [Function.comp_apply, Pi.div_apply]
  rw [dif_pos hη, canonical_inverse_formula d (by simpa using hη) hm]
  unfold denominator
  field_simp

/-- Uniform two-sided bounds, with constants chosen before the height. -/
theorem canonical_inverse_order (w : ℂ) (hw : ‖w‖=1) (hi : 0<w.im)
    (hwd : w^(2*d)=1) : ∃ r : ℝ, 0<r ∧ ∀ η : ℝ, ∀ hη : 0<η, η<r →
      (w.im/2)/η ≤ canonicalInverseNorm d (heightPoint (-2*w.re) η) (by simpa using hη) ∧
      canonicalInverseNorm d (heightPoint (-2*w.re) η) (by simpa using hη) ≤ (2*w.im)/η := by
  have hh := (canonical_inverse_exact_limit d w hw hi hwd).eventually
    (Ioo_mem_nhds (by linarith : w.im/2<w.im) (by linarith : w.im<2*w.im))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨r,hr,?_⟩
  intro η hη hηr
  have hb := hball ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hη] using hηr, hη⟩
  change w.im/2 < (if h : 0<η then η*canonicalInverseNorm d
    (heightPoint (-2*w.re) η) (by simpa using h) else 0) ∧ _ at hb
  rw [dif_pos hη] at hb
  constructor
  · exact (div_le_iff₀ hη).mpr (by nlinarith [hb.1])
  · exact (le_div_iff₀ hη).mpr (by nlinarith [hb.2])

/-- The article's full family: every directed cycle of length at least three
has sharp bulk instability at `-2*cos(2π/d)`, with constant `sin(2π/d)`. -/
theorem directed_cycle_exact_limit (hd : 3 ≤ d) :
    Tendsto (fun η : ℝ => if hη : 0<η then
      η*canonicalInverseNorm d (heightPoint (-2*Real.cos (2*Real.pi/(d : ℝ))) η)
        (by simpa using hη) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (2*Real.pi/(d : ℝ)))) := by
  have hwd : CyclicExample.cyclicOmega d ^ (2*d)=1 := by
    rw [Nat.mul_comm 2 d, pow_mul, CyclicExample.cyclicOmega_pow d (by omega), one_pow]
  simpa [CyclicExample.cyclicOmega_re, CyclicExample.cyclicOmega_im] using
    canonical_inverse_exact_limit d (CyclicExample.cyclicOmega d)
      (CyclicExample.cyclicOmega_norm d) (CyclicExample.cyclicOmega_upper d hd) hwd

end NonSymmetricDyson.Full.CyclicGeneral
