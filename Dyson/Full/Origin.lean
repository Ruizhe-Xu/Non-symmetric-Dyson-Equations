import Dyson.Full.Deflation
import Dyson.Full.BulkOriginData
import Dyson.Uniqueness
import Dyson.Full.EuclideanInverse

/-! The actual bipartite Dyson opening, including the |z|⁻¹ estimate.
Only the ordinary Perron theorem is retained as an external principle. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace NonSymmetricDyson.Full.Origin
universe u
variable {V : Type u} [Fintype V]

def stabilityCLM (S : Matrix V V ℝ) (m : V → ℂ) :
    (V → ℂ) →L[ℂ] (V → ℂ) :=
  (InteriorStability.stabilityOperator S m).toContinuousLinearMap

@[simp] theorem stabilityCLM_apply (S : Matrix V V ℝ) (m x : V → ℂ) :
    stabilityCLM S m x = InteriorStability.stabilityOperator S m x := rfl

theorem continuous_stability (S : Matrix V V ℝ) : Continuous (stabilityCLM S) := by
  apply continuous_clm_apply.mpr
  intro x
  apply continuous_pi
  intro i
  simp only [stabilityCLM_apply, InteriorStability.stabilityOperator_apply]
  fun_prop

def openingVector (t m : V → ℂ) : V → ℂ := fun i => -Complex.I * (t i * m i)
def openingRight (t m : V → ℂ) : V → ℂ := fun i => Complex.I * (t i * m i ^ 2)

theorem opening_identity (S : Matrix V V ℝ) (t m : V → ℂ) (z : ℂ)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i)
    (hm : ∀ i, m i ≠ 0)
    (hsol : BasicEstimates.IsDysonSolution S (fun _ => 0) z m) :
    stabilityCLM S m (openingVector t m) = z • openingRight t m := by
  have heq : openingVector t m = -Complex.I • BulkPerron.signMul t m := rfl
  rw [heq, map_smul]
  have hh := BulkAlgebra.bipartite_direction_identity S t m z hs hm
    (fun i => by simpa [BasicEstimates.IsDysonSolution, Model.action_apply] using hsol i)
  change (-Complex.I) • (DysonPaper.Algebra.stabilityAction m (Model.action S)
    (BulkPerron.signMul t m)) = _
  rw [show BulkPerron.signMul t m = (fun i => t i * m i) from rfl, hh]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, openingRight]
  ring

theorem openingVector_origin (t : V → ℂ) (q : V → ℝ) :
    openingVector t (BulkOriginData.imaginaryVector q) =
      BulkPerron.signMul t (fun i => (q i : ℂ)) := by
  funext i
  simp only [openingVector, BulkOriginData.imaginaryVector, BulkPerron.signMul]
  calc
    _ = -Complex.I ^ 2 * (t i * (q i : ℂ)) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem openingRight_origin (t : V → ℂ) (q : V → ℝ) :
    openingRight t (BulkOriginData.imaginaryVector q) =
      -Complex.I • BulkPerron.signMul t (fun i => (q i : ℂ) ^ 2) := by
  funext i
  simp [openingRight, BulkOriginData.imaginaryVector, BulkPerron.signMul, mul_pow]

/-- Reflection at the imaginary axis for zero potential follows from the
already proved uniqueness theorem. -/
theorem imaginary_axis_real_part_zero (S : Matrix V V ℝ) (η : ℝ) (m : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hη : 0 < η)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S (fun _ => 0) ((η : ℂ)*Complex.I) m) :
    ∀ i, (m i).re = 0 := by
  let n : V → ℂ := fun i => -star (m i)
  have hn : BasicEstimates.IsUpperSolution n := by
    intro i
    simpa [n, Complex.star_def] using hm i
  have hneq : BasicEstimates.IsDysonSolution S (fun _ => 0) ((η : ℂ)*Complex.I) n := by
    intro i
    have hh := congrArg (fun w : ℂ => -star w) (hsol i)
    simpa [n, map_sum, mul_neg, Finset.sum_neg_distrib, Complex.star_def, add_comm] using hh
  have heq := Uniqueness.upper_half_plane_unique hS (by simpa using hη) hm hn hsol hneq
  intro i
  have hh := congrArg Complex.re (congrFun heq i)
  simp [n, Complex.star_def] at hh
  linarith

theorem imaginary_boundary_of_limit (S : Matrix V V ℝ) (m : ℝ → V → ℂ) (m₀ : V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hm : ∀ η, 0 < η → BasicEstimates.IsUpperSolution (m η))
    (heq : ∀ η : ℝ, 0 < η → BasicEstimates.IsDysonSolution S (fun _ => 0)
      ((η : ℂ)*Complex.I) (m η))
    (hlim : Tendsto m (𝓝[Set.Ioi 0] 0) (𝓝 m₀)) :
    m₀ = BulkOriginData.imaginaryVector (fun i => (m₀ i).im) := by
  funext i
  have hri : Tendsto (fun η => (m η i).re) (𝓝[Set.Ioi 0] 0) (𝓝 (m₀ i).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hlim i)
  have hz : ∀ᶠ η in 𝓝[Set.Ioi 0] 0, (m η i).re = 0 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact imaginary_axis_real_part_zero S η (m η) hS hη (hm η hη) (heq η hη) i
  have hzero : (m₀ i).re = 0 := tendsto_nhds_unique hri (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  apply Complex.ext
  · simpa [BulkOriginData.imaginaryVector] using hzero
  · simp [BulkOriginData.imaginaryVector]

/-- The local |z|⁻¹ estimate is applied to the actual stability matrix and
the actual Dyson equation. The kernel and nonzero opening are consequences
of the ordinary Perron theorem, rather than additional Dyson hypotheses. -/
theorem bipartite_origin_bound [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (q : V → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in 𝓝 (BulkOriginData.imaginaryVector q),
      ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 → (∀ i, m i ≠ 0) →
        BasicEstimates.IsDysonSolution S (fun _ => 0) z m →
        ∀ x, ‖x‖ ≤ (C/‖z‖) * ‖InteriorStability.stabilityOperator S m x‖ := by
  obtain ⟨φ, hnorm, hopen, hleft, hsimple⟩ :=
    BulkOriginData.actual_origin_kernel_data external S (fun _ => 0) 0 q
      hS hc hq hsol₀ t ht hs
  have hv : Continuous (openingVector t) := by
    apply continuous_pi
    intro i
    dsimp [openingVector]
    fun_prop
  have hb : Continuous (openingRight t) := by
    apply continuous_pi
    intro i
    dsimp [openingRight]
    fun_prop
  have hn : φ (openingVector t (BulkOriginData.imaginaryVector q)) = 1 := by
    rw [openingVector_origin]; exact hnorm
  have ho : φ (openingRight t (BulkOriginData.imaginaryVector q)) ≠ 0 := by
    rw [openingRight_origin, map_smul, smul_eq_mul]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hopen
  obtain ⟨C, hC, hev⟩ := Deflation.local_linear_opening_bound
    (BulkOriginData.imaginaryVector q) (stabilityCLM S)
    (openingVector t) (openingRight t) φ
    (continuous_stability S).continuousAt hv.continuousAt hb.continuousAt hn ho
    hleft (by simpa only [openingVector_origin] using hsimple)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with m hm
  intro z hz hzle hm0 hsol x
  exact hm z hz hzle (opening_identity S t m z hs hm0 hsol) x

/-- Both sides of the origin estimate, in the paper's Euclidean norm. -/
theorem bipartite_origin_inverse [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (q : V → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ m in 𝓝 (BulkOriginData.imaginaryVector q),
      ∀ z : ℂ, ∀ hz : 0 < z.im, ‖z‖ ≤ 1 →
      ∀ hm : BasicEstimates.IsUpperSolution m,
      ∀ heq : BasicEstimates.IsDysonSolution S (fun _ => 0) z m,
      c/‖z‖ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z m hS hz hm heq‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z m hS hz hm heq‖ ≤ C/‖z‖ := by
  let m₀ := BulkOriginData.imaginaryVector q
  let v₀ := openingVector t m₀
  let b₀ := openingRight t m₀
  have hv₀ : v₀ ≠ 0 := by
    intro hz
    let i : V := Classical.arbitrary V
    have hti : t i ≠ 0 := by intro hi; have hh := ht i; simp [hi] at hh
    have hh := congrFun hz i
    rw [show v₀ = BulkPerron.signMul t (fun i => (q i : ℂ)) from openingVector_origin t q] at hh
    exact mul_ne_zero hti (Complex.ofReal_ne_zero.mpr (hq i).ne') hh
  let A := ‖v₀‖/2
  let B := Real.sqrt (Fintype.card V) * (1 + ‖b₀‖)
  have hd : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hA : 0 < A := by dsimp [A]; exact half_pos (norm_pos_iff.mpr hv₀)
  have hB : 0 < B := by dsimp [B]; positivity
  have hv : Continuous (openingVector t) := by
    apply continuous_pi; intro i; dsimp [openingVector]; fun_prop
  have hb : Continuous (openingRight t) := by
    apply continuous_pi; intro i; dsimp [openingRight]; fun_prop
  have hev : ∀ᶠ m in 𝓝 m₀, A ≤ ‖openingVector t m‖ :=
    hv.continuousAt.norm.tendsto.eventually_const_le (by dsimp [A, v₀]; linarith [norm_pos_iff.mpr hv₀])
  have heb : ∀ᶠ m in 𝓝 m₀, ‖openingRight t m‖ ≤ 1 + ‖b₀‖ :=
    hb.continuousAt.norm.tendsto.eventually_le_const (by dsimp [b₀]; linarith)
  obtain ⟨C, hC, hevC⟩ := bipartite_origin_bound external S q hS hc hq hsol₀ t ht hs
  refine ⟨A/B, Real.sqrt (Fintype.card V)*C, div_pos hA hB, mul_pos hd hC, ?_⟩
  filter_upwards [hev, heb, hevC] with m hvm hbm hCm
  intro z hz hzle hm heq
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hm0 := BasicEstimates.component_ne_zero hm
  constructor
  · apply EuclideanInverse.stability_inverse_lower S (fun _ => 0) z m hS hz hm heq
      (openingVector t m) (openingRight t m) z hz0 A B hA hB
    · exact hvm.trans (Norms.sup_le_euclidean _)
    · exact (Norms.euclidean_le_sqrt_card_mul_sup _).trans
        (mul_le_mul_of_nonneg_left hbm hd.le)
    · exact opening_identity S t m z hs hm0 heq
  · have hh := EuclideanInverse.stability_inverse_upper S (fun _ => 0) z m hS hz hm heq
      (C/‖z‖) (by positivity) (hCm z hz0 hzle hm0 heq)
    convert hh using 1 <;> ring

/-- Apply the origin estimate to a physical solution family with its actual
upper half-plane boundary limit. This supplies one fixed radius and constants. -/
theorem bipartite_origin_family_inverse [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (q : V → ℝ) (m : ℂ → V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hlim : Tendsto m (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 (BulkOriginData.imaginaryVector q))) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧
      ∀ z : ℂ, ∀ hz : 0 < z.im, ‖z‖ < r →
        c/‖z‖ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
          (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
          (hupper z hz) (heq z hz)‖ ≤ C/‖z‖ := by
  obtain ⟨c,C,hc',hC,hev⟩ := bipartite_origin_inverse external S q hS hc hq hsol₀ t ht hs
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp (hlim.eventually hev)
  refine ⟨min r 1,c,C,lt_min hr zero_lt_one,hc',hC,?_⟩
  intro z hz hzr
  have hzball : z ∈ Metric.ball (0 : ℂ) r := by
    simpa using hzr.trans_le (min_le_left _ _)
  exact hball ⟨hzball,hz⟩ z hz (hzr.trans_le (min_le_right _ _)).le
    (hupper z hz) (heq z hz)

end NonSymmetricDyson.Full.Origin
