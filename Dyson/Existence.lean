import Mathlib
import Dyson.BasicEstimates

/-!
# The Dyson fixed-point map and existence at large imaginary part

Source: the existence assertion in Theorem `thm:Existence and uniqueness`.
The compact convex invariant domain is constructed directly. The existence
theorem below uses the Banach contraction principle under an explicit
large-imaginary-part condition; it does not assert the full arbitrary-z theorem.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.Existence

open BasicEstimates

variable {ι : Type*} [Fintype ι]

/-- The affine denominator in the Dyson fixed-point map. -/
def denominator (S : ι → ι → ℝ) (a : ι → ℝ) (z : ℂ)
    (w : ι → ℂ) (i : ι) : ℂ :=
  z - (a i : ℂ) + ∑ j, (S i j : ℂ) * w j

/-- The nonlinear Dyson fixed-point map. -/
def dysonMap (S : ι → ι → ℝ) (a : ι → ℝ) (z : ℂ)
    (w : ι → ℂ) (i : ι) : ℂ := -(denominator S a z w i)⁻¹

/-- The closed upper half-disk of radius `(Im z)⁻¹` in every coordinate. -/
def admissibleSet (z : ℂ) : Set (ι → ℂ) :=
  {w | ∀ i, 0 ≤ (w i).im ∧ ‖w i‖ ≤ z.im⁻¹}

variable {S : ι → ι → ℝ} {a : ι → ℝ} {z : ℂ}

theorem denominator_im (w : ι → ℂ) (i : ι) :
    (denominator S a z w i).im = z.im + ∑ j, S i j * (w j).im := by
  simp [denominator, Complex.mul_im]

theorem denominator_im_lower (hS : ∀ i j, 0 ≤ S i j)
    {w : ι → ℂ} (hw : ∀ j, 0 ≤ (w j).im) (i : ι) :
    z.im ≤ (denominator S a z w i).im := by
  rw [denominator_im]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (hw j))

theorem denominator_ne_zero (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    {w : ι → ℂ} (hw : ∀ j, 0 ≤ (w j).im) (i : ι) :
    denominator S a z w i ≠ 0 := by
  intro h
  have hpos := lt_of_lt_of_le hz (denominator_im_lower hS hw i (a := a))
  simp [h] at hpos

theorem dysonMap_im_pos (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    {w : ι → ℂ} (hw : ∀ j, 0 ≤ (w j).im) (i : ι) :
    0 < (dysonMap S a z w i).im := by
  have hpos := lt_of_lt_of_le hz (denominator_im_lower hS hw i (a := a))
  have hn := Complex.normSq_pos.mpr (denominator_ne_zero hS hz hw i (a := a))
  simpa [dysonMap, Complex.inv_im, neg_div] using div_pos hpos hn

theorem dysonMap_norm_le (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    {w : ι → ℂ} (hw : ∀ j, 0 ≤ (w j).im) (i : ι) :
    ‖dysonMap S a z w i‖ ≤ z.im⁻¹ := by
  have hn : z.im ≤ ‖denominator S a z w i‖ :=
    (denominator_im_lower hS hw i).trans (Complex.im_le_norm _)
  simpa [dysonMap] using inv_anti₀ hz hn

theorem dysonMap_mapsTo (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im) :
    Set.MapsTo (dysonMap S a z) (admissibleSet z) (admissibleSet z) := by
  intro w hw i
  exact ⟨(dysonMap_im_pos hS hz (fun j => (hw j).1) i).le,
    dysonMap_norm_le hS hz (fun j => (hw j).1) i⟩

omit [Fintype ι] in
theorem admissibleSet_nonempty (hz : 0 < z.im) :
    (admissibleSet z : Set (ι → ℂ)).Nonempty := by
  refine ⟨0, fun i => ?_⟩
  simp only [Pi.zero_apply, Complex.zero_im, norm_zero]
  exact ⟨le_rfl, inv_nonneg.mpr hz.le⟩

omit [Fintype ι] in
theorem admissibleSet_isClosed : IsClosed (admissibleSet z : Set (ι → ℂ)) := by
  have heq : admissibleSet z = ⋂ i : ι,
      {w : ι → ℂ | 0 ≤ (w i).im} ∩ {w : ι → ℂ | ‖w i‖ ≤ z.im⁻¹} := by
    ext w
    simp [admissibleSet]
  rw [heq]
  exact isClosed_iInter fun i =>
    (isClosed_le continuous_const (Complex.continuous_im.comp (continuous_apply i))).inter
      (isClosed_le ((continuous_apply i).norm) continuous_const)

omit [Fintype ι] in
theorem admissibleSet_isCompact : IsCompact (admissibleSet z : Set (ι → ℂ)) := by
  change IsCompact {w : ι → ℂ | ∀ i, w i ∈ {u : ℂ | 0 ≤ u.im ∧ ‖u‖ ≤ z.im⁻¹}}
  apply isCompact_pi_infinite
  intro i
  have hc : IsClosed {u : ℂ | 0 ≤ u.im ∧ ‖u‖ ≤ z.im⁻¹} :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_norm continuous_const)
  exact (isCompact_closedBall (0 : ℂ) z.im⁻¹).of_isClosed_subset hc
    (fun u hu => by simpa [Metric.mem_closedBall, dist_zero_right] using hu.2)

omit [Fintype ι] in
theorem admissibleSet_convex : Convex ℝ (admissibleSet z : Set (ι → ℂ)) := by
  intro x hx y hy r s hr hs hrs i
  have him : 0 ≤ (r • x i + s • y i).im := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    exact add_nonneg (mul_nonneg hr (hx i).1) (mul_nonneg hs (hy i).1)
  have hball : r • x i + s • y i ∈ Metric.closedBall (0 : ℂ) z.im⁻¹ :=
    convex_closedBall (0 : ℂ) z.im⁻¹
      (by simpa [Metric.mem_closedBall, dist_zero_right] using (hx i).2)
      (by simpa [Metric.mem_closedBall, dist_zero_right] using (hy i).2) hr hs hrs
  exact ⟨him, by simpa [Metric.mem_closedBall, dist_zero_right] using hball⟩

theorem continuousOn_dysonMap (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im) :
    ContinuousOn (dysonMap S a z) (admissibleSet z) := by
  apply continuousOn_pi.mpr
  intro i
  have hd : Continuous (fun w : ι → ℂ => denominator S a z w i) := by
    unfold denominator
    fun_prop
  exact (hd.continuousOn.inv₀ (fun w hw =>
    denominator_ne_zero hS hz (fun j => (hw j).1) i)).neg

theorem fixedPoint_is_solution {w : ι → ℂ}
    (hw : dysonMap S a z w = w) : IsDysonSolution S a z w := by
  intro i
  have hi : -(denominator S a z w i)⁻¹ = w i := congrFun hw i
  rw [← hi]
  simp only [inv_neg, inv_inv, neg_neg]
  rfl

theorem denominator_sub (w v : ι → ℂ) (i : ι) :
    denominator S a z w i - denominator S a z v i =
      ∑ j, (S i j : ℂ) * (w j - v j) := by
  simp only [denominator, mul_sub, Finset.sum_sub_distrib]
  ring

theorem denominator_sub_norm_le (hS : ∀ i j, 0 ≤ S i j)
    (w v : ι → ℂ) (i : ι) :
    ‖denominator S a z w i - denominator S a z v i‖ ≤
      (∑ j, S i j) * ‖w - v‖ := by
  rw [denominator_sub]
  calc
    ‖∑ j, (S i j : ℂ) * (w j - v j)‖ ≤
        ∑ j, ‖(S i j : ℂ) * (w j - v j)‖ := norm_sum_le _ _
    _ = ∑ j, S i j * ‖w j - v j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i j)]
    _ ≤ ∑ j, S i j * ‖w - v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm (w - v) j) (hS i j)
    _ = (∑ j, S i j) * ‖w - v‖ := (Finset.sum_mul _ _ _).symm

/-- A direct contraction estimate when every row sum is at most `(Im z)²/2`.
Only nonnegative imaginary coordinates of the arguments are required. -/
theorem dysonMap_sub_norm_le_half (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hrow : ∀ i, ∑ j, S i j ≤ z.im ^ 2 / 2)
    {w v : ι → ℂ} (hw : ∀ j, 0 ≤ (w j).im) (hv : ∀ j, 0 ≤ (v j).im) (i : ι) :
    ‖dysonMap S a z w i - dysonMap S a z v i‖ ≤ (1 / 2 : ℝ) * ‖w - v‖ := by
  have hnw : z.im ≤ ‖denominator S a z w i‖ :=
    (denominator_im_lower hS hw i).trans (Complex.im_le_norm _)
  have hnv : z.im ≤ ‖denominator S a z v i‖ :=
    (denominator_im_lower hS hv i).trans (Complex.im_le_norm _)
  have hd : z.im ^ 2 ≤ ‖denominator S a z v i‖ * ‖denominator S a z w i‖ := by
    simpa only [pow_two] using mul_le_mul hnv hnw hz.le (norm_nonneg _)
  have hη : 0 < z.im ^ 2 := sq_pos_of_pos hz
  have heq : dysonMap S a z w i - dysonMap S a z v i =
      (denominator S a z w i - denominator S a z v i) /
        (denominator S a z v i * denominator S a z w i) := by
    simp only [dysonMap, neg_sub_neg]
    exact inv_sub_inv (denominator_ne_zero hS hz hv i) (denominator_ne_zero hS hz hw i)
  rw [heq, norm_div, norm_mul]
  calc
    ‖denominator S a z w i - denominator S a z v i‖ /
          (‖denominator S a z v i‖ * ‖denominator S a z w i‖) ≤
        ‖denominator S a z w i - denominator S a z v i‖ / z.im ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) hη hd
    _ ≤ ((∑ j, S i j) * ‖w - v‖) / z.im ^ 2 :=
      (div_le_div_iff_of_pos_right hη).mpr (denominator_sub_norm_le hS w v i)
    _ ≤ (1 / 2 : ℝ) * ‖w - v‖ := by
      apply (div_le_iff₀ hη).mpr
      have h := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg (w - v))
      nlinarith

/-- A genuine existence theorem obtained from Banach's theorem.
It applies to every finite nonnegative matrix, real shift vector, and parameter
with positive imaginary part satisfying the displayed row-sum condition. -/
theorem exists_upper_solution_large_im (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hrow : ∀ i, ∑ j, S i j ≤ z.im ^ 2 / 2) :
    ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a z m := by
  let K := admissibleSet z (ι := ι)
  have hKclosed : IsClosed K := admissibleSet_isClosed
  letI : IsClosed K := hKclosed
  letI : Nonempty K := (admissibleSet_nonempty hz).to_subtype
  let T : K → K := fun w => ⟨dysonMap S a z w, dysonMap_mapsTo hS hz w.property⟩
  have hT : ContractingWith (1 / 2 : NNReal) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun w v => ?_⟩
    change ‖dysonMap S a z w.val - dysonMap S a z v.val‖ ≤
      ((1 / 2 : NNReal) : ℝ) * ‖w.val - v.val‖
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact dysonMap_sub_norm_le_half hS hz hrow
      (fun j => (w.property j).1) (fun j => (v.property j).1) i
  let m : K := hT.fixedPoint T
  have hm : dysonMap S a z m.val = m.val :=
    congrArg Subtype.val hT.fixedPoint_isFixedPt.eq
  refine ⟨m.val, ?_, fixedPoint_is_solution hm⟩
  intro i
  rw [← congrFun hm i]
  exact dysonMap_im_pos hS hz (fun j => (m.property j).1) i

end NonSymmetricDyson.Existence
