import Mathlib
import Dyson.Full.Linear
import Dyson.GlobalWellPosedness

/-! A genuine three-cycle counterexample at the regular bulk energy 1.
The scalar branch is constructed by the ordinary complex half power,
identified with the actual canonical vector solution by uniqueness.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.CyclicExample

def cycle : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycle_nonnegative : ∀ i j, 0 ≤ cycle i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [cycle]

theorem cycle_not_symmetric : ¬ ∀ i j, cycle i j = cycle j i := by
  intro h
  have hh := h 0 1
  norm_num [cycle] at hh

theorem cycle_triangle (i j : Fin 3) :
    (cycle i j ≠ 0 ∨ cycle j i ≠ 0) ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> norm_num [cycle]

theorem cycle_irreducible (i j : Fin 3) :
    ∃ k : ℕ, 0 < k ∧ 0 < (cycle ^ k) i j := by
  classical
  refine ⟨if i = j then 3 else if cycle i j = 1 then 1 else 2, ?_, ?_⟩ <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [cycle, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply]

theorem cycle_row_sum (i : Fin 3) : ∑ j, cycle i j = 1 := by
  fin_cases i <;> norm_num [Fin.sum_univ_three, cycle, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem cycle_constant_action (c : ℂ) (i : Fin 3) :
    Model.action cycle (fun _ => c) i = c := by
  fin_cases i <;> norm_num [Model.action_apply, Fin.sum_univ_three, cycle, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

def omega : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt_three_sq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)

theorem omega_im : omega.im = Real.sqrt 3 / 2 := by simp [omega]
theorem omega_upper : 0 < omega.im := by rw [omega_im]; positivity

theorem omega_quadratic : omega^2 + omega + 1 = 0 := by
  apply Complex.ext <;> simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt_three_sq]

theorem omega_cube : omega^3 = 1 := by
  linear_combination (omega-1) * omega_quadratic

theorem omega_norm : ‖omega‖ = 1 := by
  have hn : Complex.normSq omega = 1 := by
    simp [Complex.normSq_apply, omega]
    nlinarith [sqrt_three_sq]
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg omega]

def root (z : ℂ) : ℂ := (4-z^2) ^ ((2 : ℂ)⁻¹)
def scalar (z : ℂ) : ℂ := (-z + Complex.I * root z) / 2

theorem root_square (z : ℂ) : root z ^ 2 = 4-z^2 :=
  Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)

theorem root_one : root 1 = (Real.sqrt 3 : ℂ) := by
  have hs : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast sqrt_three_sq
  have h := Complex.sq_cpow_two_inv (x := (Real.sqrt 3 : ℂ))
    (by simpa using sqrt_three_pos)
  rw [hs] at h
  simpa only [root, one_pow, show (4 : ℂ)-1=3 by norm_num] using h

theorem scalar_one : scalar 1 = omega := by
  rw [scalar, root_one]
  unfold omega
  ring

theorem scalar_quadratic (z : ℂ) : scalar z ^ 2 + z * scalar z + 1 = 0 := by
  have h := root_square z
  unfold scalar
  linear_combination -(1/4 : ℂ) * h + (root z ^ 2 / 4) * Complex.I_sq

theorem scalar_differentiable : DifferentiableAt ℂ scalar 1 := by
  have hroot : DifferentiableAt ℂ root 1 := by
    apply DifferentiableAt.cpow_const
      (differentiableAt_const 4 |>.sub (differentiableAt_id.pow 2))
    norm_num [Complex.mem_slitPlane_iff]
  exact ((differentiableAt_id.neg).add (hroot.const_mul Complex.I)).div_const 2

theorem scalar_upper_near : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < (scalar z).im := by
  have hc := Complex.continuous_im.continuousAt.comp scalar_differentiable.continuousAt
  apply hc.eventually (lt_mem_nhds (by simpa [scalar_one] using omega_upper))

theorem scalar_dyson {z : ℂ} (hm : 0 < (scalar z).im) :
    BasicEstimates.IsDysonSolution cycle (fun _ => 0) z (fun _ => scalar z) := by
  have hn : scalar z ≠ 0 := by intro h; simpa [h] using hm
  intro i
  change -(scalar z)⁻¹ = z - (0 : ℂ) + Model.action cycle (fun _ => scalar z) i
  rw [cycle_constant_action, sub_zero]
  apply (mul_left_cancel₀ hn)
  simp only [mul_neg, mul_inv_cancel₀ hn]
  linear_combination -(scalar_quadratic z)

theorem canonical_eq_scalar_near : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < z.im →
    GlobalWellPosedness.solution cycle (fun _ => 0) cycle_nonnegative z =
      fun _ => scalar z := by
  filter_upwards [scalar_upper_near] with z hz hzi
  exact GlobalWellPosedness.solution_eq_of_upper_solution (fun _ => 0) cycle_nonnegative
    hzi (fun _ => hz) (scalar_dyson hz)

def eigenvector : Fin 3 → ℂ := ![1, omega, omega^2]
def beta (z : ℂ) : ℂ := 1-scalar z^2*omega

theorem cycle_eigenvector (i : Fin 3) :
    Model.action cycle eigenvector i = omega * eigenvector i := by
  fin_cases i <;> simp [Model.action_apply, Fin.sum_univ_three, cycle, eigenvector]
  · ring
  · simpa [pow_succ, mul_assoc] using omega_cube.symm

theorem eigenvector_norm : ‖eigenvector‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> simp [eigenvector, norm_pow, omega_norm]
  · have h := norm_le_pi_norm eigenvector (0 : Fin 3)
    simpa [eigenvector] using h

theorem stability_eigenvector (z : ℂ) :
    InteriorStability.stabilityOperator cycle (fun _ => scalar z) eigenvector =
      beta z • eigenvector := by
  ext i
  change eigenvector i - scalar z^2 * Model.action cycle eigenvector i = _
  rw [cycle_eigenvector]
  simp only [Pi.smul_apply, smul_eq_mul, beta]
  ring

theorem beta_one : beta 1 = 0 := by
  simp only [beta, scalar_one]
  have h := omega_cube
  linear_combination -h

theorem beta_linear_upper : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ z in 𝓝 (1 : ℂ), ‖beta z‖ ≤ C * ‖z-1‖ := by
  have hd : DifferentiableAt ℂ beta 1 :=
    differentiableAt_const 1 |>.sub ((scalar_differentiable.pow 2).mul_const omega)
  obtain ⟨C, hC, hc⟩ := hd.hasDerivAt.isBigO_sub.exists_pos
  refine ⟨C, hC, ?_⟩
  simpa [beta_one] using hc.bound

theorem cycle_not_bipartite : ¬ ∃ part : Fin 3 → Bool,
    ∀ i j, (cycle i j ≠ 0 ∨ cycle j i ≠ 0) → part i ≠ part j := by
  rintro ⟨part, h⟩
  have h01 := h 0 1 ((cycle_triangle 0 1).mpr (by decide))
  have h12 := h 1 2 ((cycle_triangle 1 2).mpr (by decide))
  have h20 := h 2 0 ((cycle_triangle 2 0).mpr (by decide))
  cases h0 : part 0 <;> cases h1 : part 1 <;> cases h2 : part 2 <;> simp_all

theorem scalar_norm_near : ∀ᶠ z in 𝓝 (1 : ℂ),
    1/2 ≤ ‖scalar z‖ ∧ ‖scalar z‖ ≤ 2 := by
  have hc := scalar_differentiable.continuousAt.norm
  have hlo : ∀ᶠ z in 𝓝 (1 : ℂ), 1/2 < ‖scalar z‖ :=
    hc.eventually (lt_mem_nhds (by simpa only [scalar_one, omega_norm] using (by norm_num : (1:ℝ)/2<1)))
  have hhi : ∀ᶠ z in 𝓝 (1 : ℂ), ‖scalar z‖ < 2 :=
    hc.eventually (gt_mem_nhds (by simpa only [scalar_one, omega_norm] using (by norm_num : (1:ℝ)<2)))
  filter_upwards [hlo, hhi] with z hz hw using ⟨hz.le, hw.le⟩

def scalarInverseNorm (z : ℂ) (hz : 0 < z.im) (hm : 0 < (scalar z).im) : ℝ :=
  ‖(InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (fun _ => hm) (scalar_dyson hm)).symm.toContinuousLinearMap‖

def canonicalInverseNorm (z : ℂ) (hz : 0 < z.im) : ℝ :=
  ‖(InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (GlobalWellPosedness.solution_upper (fun _ => 0) cycle_nonnegative hz)
    (GlobalWellPosedness.solution_equation (fun _ => 0) cycle_nonnegative hz)).symm.toContinuousLinearMap‖

theorem canonicalInverseNorm_eq (z : ℂ) (hz : 0 < z.im) (hm : 0 < (scalar z).im) :
    canonicalInverseNorm z hz = scalarInverseNorm z hz hm := by
  have he := GlobalWellPosedness.solution_eq_of_upper_solution (fun _ => 0)
    cycle_nonnegative hz (fun _ => hm) (scalar_dyson hm)
  have heq : InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
      (GlobalWellPosedness.solution_upper (fun _ => 0) cycle_nonnegative hz)
      (GlobalWellPosedness.solution_equation (fun _ => 0) cycle_nonnegative hz) =
      InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
        (fun _ => hm) (scalar_dyson hm) := by
    ext u i
    change InteriorStability.stabilityOperator cycle _ u i =
      InteriorStability.stabilityOperator cycle _ u i
    rw [he]
  unfold canonicalInverseNorm scalarInverseNorm
  rw [heq]

theorem scalar_gap {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im)
    (hlo : 1/2 ≤ ‖scalar z‖) (hhi : ‖scalar z‖ ≤ 2) :
    z.im / 8 ≤ 1 - ‖scalar z‖^2 ∧ ‖scalar z‖^2 < 1 := by
  have hi := BasicEstimates.imaginary_part_identity_sq_norm (scalar_dyson hm) 0
  have hsum : (∑ j : Fin 3, cycle 0 j * (scalar z).im) = (scalar z).im := by
    rw [← Finset.sum_mul, cycle_row_sum, one_mul]
  change (scalar z).im / ‖scalar z‖^2 = z.im + ∑ j, cycle 0 j * (scalar z).im at hi
  rw [hsum] at hi
  have hq : 0 < ‖scalar z‖^2 := by nlinarith [norm_nonneg (scalar z)]
  have hid : (1-‖scalar z‖^2) * (scalar z).im = z.im * ‖scalar z‖^2 := by
    have hh := (div_eq_iff hq.ne').mp hi
    nlinarith
  have hg : 0 < 1-‖scalar z‖^2 :=
    (mul_pos_iff_of_pos_right hm).mp (hid ▸ mul_pos hz hq)
  have hqm : 1/4 ≤ ‖scalar z‖^2 := by nlinarith [norm_nonneg (scalar z)]
  have hy : (scalar z).im ≤ 2 := (Complex.im_le_norm _).trans hhi
  have h1 := mul_le_mul_of_nonneg_left hqm hz.le
  have h2 := mul_le_mul_of_nonneg_left hy hg.le
  constructor <;> nlinarith

theorem scalar_inverse_upper {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im)
    (hlo : 1/2 ≤ ‖scalar z‖) (hhi : ‖scalar z‖ ≤ 2) :
    scalarInverseNorm z hz hm ≤ 8 / z.im := by
  obtain ⟨hgap, hq⟩ := scalar_gap hz hm hlo hhi
  have hg : 0 < 1-‖scalar z‖^2 := sub_pos.mpr hq
  apply Linear.inverse_norm_of_lower_bound cycle (fun _ => 0) z (fun _ => scalar z)
    cycle_nonnegative hz (fun _ => hm) (scalar_dyson hm) (8/z.im) (by positivity)
  intro u
  have hb := Linear.row_lower_norm_bound cycle (fun _ => scalar z) (‖scalar z‖^2)
    cycle_nonnegative hq (fun i => by rw [cycle_row_sum, mul_one]) u
  calc
    ‖u‖ ≤ ‖InteriorStability.stabilityOperator cycle (fun _ => scalar z) u‖ /
        (1-‖scalar z‖^2) := hb
    _ ≤ (8 / z.im) * ‖InteriorStability.stabilityOperator cycle (fun _ => scalar z) u‖ := by
      rw [div_le_iff₀ hg]
      have h8 : z.im ≤ 8 * (1-‖scalar z‖^2) := by linarith
      have hb8 : 1 ≤ (8/z.im) * (1-‖scalar z‖^2) := by
        have hd := div_le_div_of_nonneg_right h8 hz.le
        rw [div_self hz.ne'] at hd
        convert hd using 1 <;> ring
      nlinarith [mul_le_mul_of_nonneg_right hb8
        (norm_nonneg (InteriorStability.stabilityOperator cycle (fun _ => scalar z) u))]

theorem scalar_inverse_lower {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im)
    {C : ℝ} (hC : 0 < C) (hb : ‖beta z‖ ≤ C * ‖z-1‖) :
    (1/C) / ‖z-1‖ ≤ scalarInverseNorm z hz hm := by
  let e := InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (fun _ => hm) (scalar_dyson hm)
  have hh := e.symm.toContinuousLinearMap.le_opNorm (e eigenvector)
  have he : e eigenvector = beta z • eigenvector := stability_eigenvector z
  have hn : 1 ≤ scalarInverseNorm z hz hm * ‖beta z‖ := by
    change ‖e.symm (e eigenvector)‖ ≤ _ at hh
    rw [e.symm_apply_apply, eigenvector_norm, he, norm_smul, eigenvector_norm, mul_one] at hh
    exact hh
  have hdist : 0 < ‖z-1‖ := by
    apply norm_pos_iff.mpr
    intro heq
    have hzz : z = 1 := sub_eq_zero.mp heq
    simp [hzz] at hz
  have hnorm : 0 ≤ scalarInverseNorm z hz hm := norm_nonneg _
  apply (div_le_iff₀ hdist).mpr
  apply (div_le_iff₀ hC).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb hnorm]

def heightPoint (η : ℝ) : ℂ := 1+(η : ℂ)*Complex.I

@[simp] theorem heightPoint_im (η : ℝ) : (heightPoint η).im = η := by
  simp [heightPoint]

theorem heightPoint_distance {η : ℝ} (hη : 0 < η) : ‖heightPoint η-1‖ = η := by
  simp [heightPoint, norm_mul, abs_of_pos hη]

theorem heightPoint_tendsto : Tendsto heightPoint (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hc : Continuous heightPoint := by unfold heightPoint; fun_prop
  have hl := hc.continuousAt (x := (0 : ℝ))
  simpa [heightPoint] using hl.tendsto.mono_left nhdsWithin_le_nhds

/-- The actual canonical solution has a positive imaginary boundary value at
energy 1, even though its stability inverse diverges there. -/
theorem canonical_boundary_limit :
    Tendsto (fun η : ℝ => GlobalWellPosedness.solution cycle (fun _ => 0)
      cycle_nonnegative (heightPoint η)) (𝓝[>] (0 : ℝ)) (𝓝 (fun _ => omega)) := by
  have he := heightPoint_tendsto.eventually canonical_eq_scalar_near
  have hp : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have heq : (fun η : ℝ => GlobalWellPosedness.solution cycle (fun _ => 0)
      cycle_nonnegative (heightPoint η)) =ᶠ[𝓝[>] 0]
      (fun η => fun _ : Fin 3 => scalar (heightPoint η)) := by
    filter_upwards [he, hp] with η hη hpos using hη (by simpa)
  apply Tendsto.congr' heq.symm
  apply tendsto_pi_nhds.mpr
  intro i
  simpa [scalar_one] using scalar_differentiable.continuousAt.tendsto.comp heightPoint_tendsto

/-- Two-sided divergence of the genuine canonical inverse operator. The norm
here is the operator norm induced by the coordinate supremum norm. -/
theorem canonical_inverse_order : ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧
    ∀ η : ℝ, ∀ hη : 0 < η, η < r →
      c / η ≤ canonicalInverseNorm (heightPoint η) (by simpa) ∧
      canonicalInverseNorm (heightPoint η) (by simpa) ≤ C / η := by
  obtain ⟨B, hB, hb⟩ := beta_linear_upper
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < (scalar z).im ∧
      (1/2 ≤ ‖scalar z‖ ∧ ‖scalar z‖ ≤ 2) ∧ ‖beta z‖ ≤ B * ‖z-1‖ := by
    filter_upwards [scalar_upper_near, scalar_norm_near, hb] with z hm hn hb using ⟨hm, hn, hb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨1/B, 8, r, by positivity, by norm_num, hr, ?_⟩
  intro η hη hηr
  have hmem : heightPoint η ∈ Metric.ball (1 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_eq_norm, heightPoint_distance hη] using hηr
  obtain ⟨hm, hn, hb⟩ := hball hmem
  have hz : 0 < (heightPoint η).im := by simpa
  rw [canonicalInverseNorm_eq _ hz hm]
  constructor
  · simpa only [heightPoint_distance hη] using scalar_inverse_lower hz hm hB hb
  · simpa only [heightPoint_im] using scalar_inverse_upper hz hm hn.1 hn.2

/-- The same linear operator expressed on the actual Euclidean normed space. -/
def euclideanMap (f : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) :
    EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    (f.comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).toContinuousLinearMap)

theorem euclideanMap_apply (f : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) (u : Fin 3 → ℂ) :
    euclideanMap f (WithLp.toLp 2 u) = WithLp.toLp 2 (f u) := rfl

theorem euclideanMap_upper (f : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) :
    ‖euclideanMap f‖ ≤ Real.sqrt 3 * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change Norms.euclideanNorm (f (WithLp.ofLp u)) ≤ _
  calc
    Norms.euclideanNorm (f (WithLp.ofLp u)) ≤ Real.sqrt 3 * ‖f (WithLp.ofLp u)‖ := by
      simpa using Norms.euclidean_le_sqrt_card_mul_sup (f (WithLp.ofLp u))
    _ ≤ Real.sqrt 3 * (‖f‖ * ‖WithLp.ofLp u‖) :=
      mul_le_mul_of_nonneg_left (f.le_opNorm _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 3 * (‖f‖ * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Norms.sup_le_euclidean (WithLp.ofLp u)
    _ = _ := by ring

theorem euclideanMap_lower (f : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ)) :
    ‖f‖ ≤ Real.sqrt 3 * ‖euclideanMap f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    ‖f u‖ ≤ Norms.euclideanNorm (f u) := Norms.sup_le_euclidean _
    _ = ‖euclideanMap f (WithLp.toLp 2 u)‖ := rfl
    _ ≤ ‖euclideanMap f‖ * Norms.euclideanNorm u := (euclideanMap f).le_opNorm _
    _ ≤ ‖euclideanMap f‖ * (Real.sqrt 3 * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using Norms.euclidean_le_sqrt_card_mul_sup u
    _ = _ := by ring

def canonicalEuclideanInverseNorm (z : ℂ) (hz : 0 < z.im) : ℝ :=
  ‖euclideanMap ((InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (GlobalWellPosedness.solution_upper (fun _ => 0) cycle_nonnegative hz)
    (GlobalWellPosedness.solution_equation (fun _ => 0) cycle_nonnegative hz)).symm.toContinuousLinearMap)‖

/-- The counterexample in the manuscript's actual Euclidean operator norm. -/
theorem canonical_euclidean_inverse_order : ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧
    ∀ η : ℝ, ∀ hη : 0 < η, η < r →
      c / η ≤ canonicalEuclideanInverseNorm (heightPoint η) (by simpa) ∧
      canonicalEuclideanInverseNorm (heightPoint η) (by simpa) ≤ C / η := by
  obtain ⟨c, C, r, hc, hC, hr, h⟩ := canonical_inverse_order
  refine ⟨c / Real.sqrt 3, Real.sqrt 3 * C, r, div_pos hc sqrt_three_pos,
    mul_pos sqrt_three_pos hC, hr, ?_⟩
  intro η hη hηr
  obtain ⟨hlo, hhi⟩ := h η hη hηr
  have hu : canonicalEuclideanInverseNorm (heightPoint η) (by simpa) ≤
      Real.sqrt 3 * canonicalInverseNorm (heightPoint η) (by simpa) := euclideanMap_upper _
  have hl : canonicalInverseNorm (heightPoint η) (by simpa) ≤
      Real.sqrt 3 * canonicalEuclideanInverseNorm (heightPoint η) (by simpa) := euclideanMap_lower _
  constructor
  · have hh : c/η ≤ Real.sqrt 3 * canonicalEuclideanInverseNorm (heightPoint η) (by simpa) :=
      hlo.trans hl
    have hh' : (c/η)/Real.sqrt 3 ≤ canonicalEuclideanInverseNorm (heightPoint η) (by simpa) :=
      (div_le_iff₀ sqrt_three_pos).mpr (by simpa only [mul_comm] using hh)
    convert hh' using 1 <;> ring
  · calc
      _ ≤ Real.sqrt 3 * canonicalInverseNorm (heightPoint η) (by simpa) := hu
      _ ≤ Real.sqrt 3 * (C/η) := mul_le_mul_of_nonneg_left hhi (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- The local branch is holomorphic across the real bulk point. -/
theorem scalar_analytic : AnalyticAt ℂ scalar 1 := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hc : Continuous (fun z : ℂ => 4-z^2) := by fun_prop
  have hs : (4-(1 : ℂ)^2) ∈ Complex.slitPlane := by
    norm_num [Complex.mem_slitPlane_iff]
  have hev := hc.continuousAt (x := (1 : ℂ)) |>.eventually
    (Complex.isOpen_slitPlane.mem_nhds hs)
  filter_upwards [hev] with z hz
  have hroot : DifferentiableAt ℂ root z := by
    exact DifferentiableAt.cpow_const
      (differentiableAt_const 4 |>.sub (differentiableAt_id.pow 2)) hz
  exact ((differentiableAt_id.neg).add (hroot.const_mul Complex.I)).div_const 2

/-- Implicit differentiation is checked against the actual scalar polynomial. -/
theorem scalar_deriv : deriv scalar 1 = -omega / ((Real.sqrt 3 : ℂ)*Complex.I) := by
  have hd := ((scalar_differentiable.hasDerivAt.pow 2).add
    ((hasDerivAt_id (1 : ℂ)).mul scalar_differentiable.hasDerivAt)).add_const 1
  have hzfun : (fun z : ℂ => scalar z^2+z*scalar z+1) = fun _ => 0 :=
    funext scalar_quadratic
  change HasDerivAt (fun z : ℂ => scalar z^2+z*scalar z+1) _ 1 at hd
  rw [hzfun] at hd
  have he := hd.unique (hasDerivAt_const (1 : ℂ) (0 : ℂ))
  norm_num [scalar_one] at he
  have hcoef : 2*omega+1 = (Real.sqrt 3 : ℂ)*Complex.I := by unfold omega; ring
  have hn : (Real.sqrt 3 : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast sqrt_three_pos.ne') Complex.I_ne_zero
  apply (eq_div_iff hn).mpr
  rw [← hcoef]
  linear_combination he

/-- The vanishing stability eigenvalue has nonzero derivative. -/
theorem beta_hasDerivAt : HasDerivAt beta (2/((Real.sqrt 3 : ℂ)*Complex.I)) 1 := by
  have hb := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    ((scalar_differentiable.hasDerivAt.pow 2).mul_const omega)
  have hn : (Real.sqrt 3 : ℂ)*Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast sqrt_three_pos.ne') Complex.I_ne_zero
  convert hb using 1
  rw [scalar_one, scalar_deriv]
  field_simp
  linear_combination -2 * omega_cube

end NonSymmetricDyson.Full.CyclicExample
