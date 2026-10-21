import Dyson.Full.CyclicExample

/-! Exact Euclidean leading constant for the actual three-cycle counterexample.
The proof uses the finite geometric inverse identity, not an assumed Fourier
spectral formula. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.CyclicExample

abbrev E := EuclideanSpace ℂ (Fin 3)

def cycleMap : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap (Model.action cycle)

def cycleEuclidean : E →L[ℂ] E := euclideanMap cycleMap

theorem cycle_action_explicit (u : Fin 3 → ℂ) :
    Model.action cycle u = ![u 1, u 2, u 0] := by
  ext i
  fin_cases i <;> norm_num [Model.action_apply, cycle, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem cycleEuclidean_apply (u : E) :
    cycleEuclidean u = WithLp.toLp 2 (Model.action cycle (WithLp.ofLp u)) := rfl

theorem cycleEuclidean_isometry (u : E) : ‖cycleEuclidean u‖ = ‖u‖ := by
  have hsq : ‖cycleEuclidean u‖^2 = ‖u‖^2 := by
    rw [cycleEuclidean_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply]
    rw [cycle_action_explicit]
    simp [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  nlinarith [norm_nonneg (cycleEuclidean u), norm_nonneg u]

theorem cycleEuclidean_norm_le : ‖cycleEuclidean‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [cycleEuclidean_isometry, one_mul]

def numerator (z : ℂ) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E + scalar z^2 • cycleEuclidean +
    scalar z^4 • (cycleEuclidean.comp cycleEuclidean)

theorem numerator_continuous : ContinuousAt numerator 1 := by
  exact ((continuousAt_const.add (scalar_differentiable.continuousAt.pow 2 |>.smul
    continuousAt_const))).add (scalar_differentiable.continuousAt.pow 4 |>.smul continuousAt_const)

theorem numerator_eigenvector :
    numerator 1 (WithLp.toLp 2 eigenvector) = (3 : ℂ) • WithLp.toLp 2 eigenvector := by
  have hp : cycleEuclidean (WithLp.toLp 2 eigenvector) =
      omega • WithLp.toLp 2 eigenvector := by
    ext i
    exact cycle_eigenvector i
  simp only [numerator, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, scalar_one, hp, map_smul]
  rw [smul_smul, smul_smul, smul_smul]
  have h3 : omega^2*omega=1 := by simpa [pow_succ] using omega_cube
  have h6 : omega^4*omega*omega=1 := by
    calc
      _ = (omega^3)^2 := by ring
      _ = 1 := by rw [omega_cube]; norm_num
  rw [h3, h6, one_smul]
  module

theorem numerator_norm_one : ‖numerator 1‖ = 3 := by
  have hp := cycleEuclidean_norm_le
  have hpp : ‖cycleEuclidean.comp cycleEuclidean‖ ≤ 1 := by
    calc
      _ ≤ ‖cycleEuclidean‖*‖cycleEuclidean‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg cycleEuclidean]
  have hu : ‖numerator 1‖ ≤ 3 := by
    have h1 := norm_add_le (ContinuousLinearMap.id ℂ E) (omega^2 • cycleEuclidean)
    have h2 := norm_add_le (ContinuousLinearMap.id ℂ E + omega^2 • cycleEuclidean)
      (omega^4 • cycleEuclidean.comp cycleEuclidean)
    norm_num [norm_smul, norm_pow, omega_norm] at h1 h2
    simp only [numerator, scalar_one]
    linarith
  have hv : 0 < ‖WithLp.toLp 2 eigenvector‖ := by
    have h := Norms.sup_le_euclidean eigenvector
    rw [eigenvector_norm] at h
    exact lt_of_lt_of_le (by norm_num) h
  have hl := (numerator 1).le_opNorm (WithLp.toLp 2 eigenvector)
  rw [numerator_eigenvector, norm_smul] at hl
  norm_num at hl
  exact le_antisymm hu (by nlinarith)

def denominator (z : ℂ) : ℂ := 1-scalar z^6

theorem denominator_one : denominator 1 = 0 := by
  have h6 : omega^6 = 1 := by
    calc
      _ = (omega^3)^2 := by ring
      _ = 1 := by rw [omega_cube]; norm_num
  simp [denominator, scalar_one, h6]

theorem denominator_hasDerivAt : HasDerivAt denominator
    (6/((Real.sqrt 3 : ℂ)*Complex.I)) 1 := by
  have hd := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    (scalar_differentiable.hasDerivAt.pow 6)
  convert hd using 1
  rw [scalar_one, scalar_deriv]
  norm_num
  field_simp
  have h6 : omega^6 = 1 := by
    calc
      _ = (omega^3)^2 := by ring
      _ = 1 := by rw [omega_cube]; norm_num
  rw [h6]

theorem denominator_ne_zero {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im)
    (hlo : 1/2 ≤ ‖scalar z‖) (hhi : ‖scalar z‖ ≤ 2) : denominator z ≠ 0 := by
  have hq := (scalar_gap hz hm hlo hhi).2
  have hn : ‖scalar z‖ < 1 := by nlinarith [norm_nonneg (scalar z)]
  have h6 := pow_lt_one₀ (norm_nonneg (scalar z)) hn (by decide : (6 : ℕ) ≠ 0)
  intro he
  have hx : scalar z^6=1 := (sub_eq_zero.mp he).symm
  have hh := congrArg norm hx
  simp only [norm_pow, norm_one] at hh
  linarith

/-- Finite geometric-series identity for the actual inverse, checked componentwise. -/
theorem scalar_inverse_explicit {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im)
    (hd : denominator z ≠ 0) (u : Fin 3 → ℂ) :
    (InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
      (fun _ => hm) (scalar_dyson hm)).symm u =
    (denominator z)⁻¹ • (u + scalar z^2 • Model.action cycle u +
      scalar z^4 • Model.action cycle (Model.action cycle u)) := by
  let e := InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (fun _ => hm) (scalar_dyson hm)
  apply e.injective
  rw [e.apply_symm_apply]
  change u = InteriorStability.stabilityOperator cycle (fun _ => scalar z) _
  ext i
  simp only [InteriorStability.stabilityOperator_apply]
  change u i = _ - scalar z^2 * Model.action cycle _ i
  simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [cycle_action_explicit]
  fin_cases i <;> simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    denominator] at hd ⊢ <;> field_simp <;> ring

theorem scalar_euclidean_inverse_explicit {z : ℂ} (hz : 0 < z.im)
    (hm : 0 < (scalar z).im) (hd : denominator z ≠ 0) :
    euclideanMap ((InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
      (fun _ => hm) (scalar_dyson hm)).symm.toContinuousLinearMap) =
      (denominator z)⁻¹ • numerator z := by
  apply ContinuousLinearMap.ext
  intro u
  change WithLp.toLp 2 ((InteriorStability.stabilityContinuousEquiv cycle_nonnegative hz
    (fun _ => hm) (scalar_dyson hm)).symm (WithLp.ofLp u)) = _
  rw [scalar_inverse_explicit hz hm hd]
  ext i
  rfl

theorem canonical_euclidean_inverse_formula {z : ℂ} (hz : 0 < z.im)
    (hm : 0 < (scalar z).im) (hd : denominator z ≠ 0) :
    canonicalEuclideanInverseNorm z hz = ‖numerator z‖ / ‖denominator z‖ := by
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
  unfold canonicalEuclideanInverseNorm
  rw [heq, scalar_euclidean_inverse_explicit hz hm hd, norm_smul, norm_inv]
  ring

theorem denominator_height_limit :
    Tendsto (fun η : ℝ => ‖denominator (heightPoint η)‖ / η)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.sqrt 3)) := by
  have hp : Tendsto heightPoint (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨heightPoint_tendsto, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    change heightPoint η ≠ 1
    intro he
    have hh := congrArg Complex.im he
    simpa using (ne_of_gt hη) (by simpa using hh)
  have hs := (hasDerivAt_iff_tendsto_slope.mp denominator_hasDerivAt).comp hp
  have hn : ‖6/((Real.sqrt 3 : ℂ)*Complex.I)‖ = 2*Real.sqrt 3 := by
    rw [norm_div, norm_mul]
    norm_num [Complex.norm_real, abs_of_pos sqrt_three_pos]
    apply (div_eq_iff sqrt_three_pos.ne').mpr
    nlinarith [sqrt_three_sq]
  have ht := hs.norm
  rw [hn] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  simp only [Function.comp_apply, slope, denominator_one, vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv,
    heightPoint_distance hη]
  ring

/-- The counterexample's exact leading constant, for the actual canonical
Dyson inverse in ordinary Euclidean operator norm. -/
theorem canonical_euclidean_exact_limit :
    Tendsto (fun η : ℝ => if hη : 0 < η then
      η * canonicalEuclideanInverseNorm (heightPoint η) (by simpa using hη) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 3 / 2)) := by
  have hn := numerator_continuous.norm.tendsto.comp heightPoint_tendsto
  rw [numerator_norm_one] at hn
  have hd := hn.div denominator_height_limit (by positivity : 2*Real.sqrt 3 ≠ 0)
  have hc : (3:ℝ)/(2*Real.sqrt 3) = Real.sqrt 3/2 := by
    apply (div_eq_iff (by positivity : 2*Real.sqrt 3 ≠ 0)).mpr
    nlinarith [sqrt_three_sq]
  rw [hc] at hd
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin, heightPoint_tendsto.eventually scalar_upper_near,
    heightPoint_tendsto.eventually scalar_norm_near] with η hη hm hnorm
  change 0 < η at hη
  dsimp only [Function.comp_apply, Pi.div_apply]
  rw [dif_pos hη, canonical_euclidean_inverse_formula (by simpa using hη) hm
    (denominator_ne_zero (by simpa using hη) hm hnorm.1 hnorm.2)]
  field_simp

end NonSymmetricDyson.Full.CyclicExample
