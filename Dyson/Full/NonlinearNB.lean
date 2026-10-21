import Dyson.Full.NonlinearBalance
import Dyson.Full.BulkDyson
import Dyson.Full.Origin

/-! The actual non-backtracking vertex balance detects the bipartite kernel. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def vertexFunctional (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T v : κ → ℂ) :
    (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (T i * v i ^ 2) • ((ContinuousLinearMap.proj i).comp B)

@[simp] theorem vertexFunctional_apply
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T v : κ → ℂ) (u : ι → ℂ) :
    vertexFunctional B T v u = ∑ i, T i * v i ^ 2 * B u i := by
  simp [vertexFunctional, smul_eq_mul]

theorem continuous_vertexFunctional (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T : κ → ℂ) :
    Continuous (vertexFunctional B T) := by
  apply continuous_clm_apply.mpr
  intro u
  simp only [vertexFunctional_apply]
  fun_prop

theorem vertexFunctional_balanceLinear
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T d : κ → ℂ) (u : ι → ℂ) :
    vertexFunctional B T (fun i => -(d i)⁻¹) u = vertexBalanceLinear B T d u := by
  simp only [vertexFunctional_apply, vertexBalanceLinear]

namespace NB

open Nonbacktracking

universe u
variable {V : Type u} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

/-- The actual outgoing incidence operator used in vertex reconstruction. -/
def incidence : (G.Edge → ℂ) →L[ℂ] (V → ℂ) :=
  ({ toFun := BulkDyson.NB.outgoingSum G
     map_add' := by
       intro x y
       funext i
       simp only [BulkDyson.NB.outgoingSum, Pi.add_apply]
       rw [← Finset.sum_add_distrib]
       apply Finset.sum_congr rfl
       intro e _
       split_ifs <;> simp
     map_smul' := by
       intro c x
       funext i
       simp only [BulkDyson.NB.outgoingSum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
       rw [Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro e _
       split_ifs <;> simp } : (G.Edge → ℂ) →ₗ[ℂ] (V → ℂ)).toContinuousLinearMap

@[simp] theorem incidence_apply (m : G.Edge → ℂ) (y : V) :
    incidence G m y = BulkDyson.NB.outgoingSum G m y := rfl

def vertexValues (m : G.Edge → ℂ) (z : ℂ) : V → ℂ :=
  fun y => -(z + incidence G m y)⁻¹

theorem incidence_signed (T : V → ℂ) (m : G.Edge → ℂ)
    (hflip : ∀ x y, G.Adj x y → T y = -T x) (y : V) :
    incidence G (fun e => T (G.head e) * m e) y = -T y * incidence G m y := by
  classical
  simp only [incidence_apply, BulkDyson.NB.outgoingSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.tail e = y
  · have ht := hflip (G.tail e) (G.head e) e.property
    simp only [he] at ht
    simp [he, ht]
  · simp [he]

theorem vertexValues_upper (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y) (y : V) :
    0 < (vertexValues G m 0 y).im := by
  obtain ⟨e, he⟩ := hdegree y
  have hh := BulkDyson.NB.outgoingSum_im_pos G m hm (G.reverse e)
  simp only [G.reverse_head, he] at hh
  have hh' : 0 < (incidence G m y).im := hh
  change 0 < (-(0 + incidence G m y)⁻¹).im
  simp only [zero_add, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hh (Complex.normSq_pos.mpr (by
    intro hz
    rw [hz] at hh'
    norm_num at hh'))

/-- The signed vertex functional on the actual bipartite kernel is exactly
the sum of the physical vertex values. -/
theorem vertexFunctional_signed_identity (T : V → ℂ) (m : G.Edge → ℂ)
    (hT : ∀ y, T y ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → T y = -T x)
    (hd : ∀ y, incidence G m y ≠ 0) :
    vertexFunctional (incidence G) T (vertexValues G m 0)
      (fun e => T (G.head e) * m e) = ∑ y, vertexValues G m 0 y := by
  rw [vertexFunctional_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [incidence_signed G T m hflip]
  simp only [vertexValues, zero_add]
  calc
    _ = -(T y ^ 2) * ((incidence G m y)⁻¹ * incidence G m y) *
        (incidence G m y)⁻¹ := by ring
    _ = _ := by rw [hT y, inv_mul_cancel₀ (hd y)]; ring

theorem vertexFunctional_detects_origin [Nonempty V]
    (T : V → ℂ) (q : G.Edge → ℝ)
    (hT : ∀ y, T y ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → T y = -T x)
    (hq : ∀ e, 0 < q e)
    (hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y) :
    vertexFunctional (incidence G) T
      (vertexValues G (BulkOriginData.imaginaryVector q) 0)
      (BulkPerron.signMul (fun e => T (G.head e)) (fun e => (q e : ℂ))) ≠ 0 := by
  let m := BulkOriginData.imaginaryVector q
  have hm : BasicEstimates.IsUpperSolution m := by
    intro e
    simpa [m, BulkOriginData.imaginaryVector, Complex.mul_im] using hq e
  have hd : ∀ y, incidence G m y ≠ 0 := by
    intro y
    obtain ⟨e, he⟩ := hdegree y
    have hh := BulkDyson.NB.outgoingSum_im_pos G m hm (G.reverse e)
    simp only [G.reverse_head, he] at hh
    intro hz
    simpa [← incidence_apply, hz] using hh
  have hsum : (∑ y, vertexValues G m 0 y) ≠ 0 := by
    apply vertex_balance_coefficient_ne_zero
    exact vertexValues_upper G m hm hdegree
  have he : (fun e => T (G.head e) * m e) = Complex.I •
      BulkPerron.signMul (fun e => T (G.head e)) (fun e => (q e : ℂ)) := by
    funext e
    simp only [m, BulkOriginData.imaginaryVector, Pi.smul_apply, smul_eq_mul, BulkPerron.signMul]
    ring
  have hidentity := vertexFunctional_signed_identity G T m hT hflip hd
  rw [he, map_smul, smul_eq_mul] at hidentity
  intro hzero
  apply hsum
  rw [← hidentity]
  change Complex.I * _ = 0
  rw [hzero, mul_zero]

/-- The graph bipartition gives the alternating sign on every non-backtracking
transition, exactly with the paper's head-vertex convention. -/
theorem transition_sign_flip (T : V → ℂ)
    (hflip : ∀ x y, G.Adj x y → T y = -T x) :
    ∀ e f, G.matrix e f ≠ 0 → T (G.head f) = -T (G.head e) := by
  classical
  intro e f hef
  have hfollow : G.CanFollow e f := by
    by_contra hn
    simp [BaseGraph.matrix, hn] at hef
  rw [hfollow.1]
  exact hflip (G.tail f) (G.head f) f.property

theorem continuousAt_vertexValues (m : G.Edge → ℂ) (z : ℂ)
    (hd : ∀ y, z + incidence G m y ≠ 0) :
    ContinuousAt (fun t : (G.Edge → ℂ) × ℂ => vertexValues G t.1 t.2) (m, z) := by
  apply continuousAt_pi.mpr
  intro y
  exact (((continuous_snd.add ((continuous_apply y).comp
    ((incidence G).continuous.comp continuous_fst))).continuousAt).inv₀ (hd y)).neg

/-- A uniform augmented linear bound in a full neighborhood of the actual
bipartite origin. Its scalar functional is the derivative of reconstructed
vertex balance; it is not an assumed replacement stability estimate. -/
theorem origin_vertex_augmented_bound [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : G.Edge → ℝ) (T : V → ℂ)
    (hconn : Resonance.StronglyConnected (fun e f => 0 < G.matrix e f))
    (hq : ∀ e, 0 < q e)
    (hT : ∀ y, T y ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → T y = -T x)
    (hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ t : (G.Edge → ℂ) × ℂ in 𝓝 (BulkOriginData.imaginaryVector q, 0),
      ∀ u, ‖u‖ ≤ A *
        (‖DysonPaper.Algebra.stabilityAction t.1 (Model.action G.matrix) u‖ +
          ‖vertexBalanceLinear (incidence G) T (fun y => t.2 + incidence G t.1 y) u‖) := by
  letI : Nonempty G.Edge := ⟨(hdegree (Classical.arbitrary V)).choose⟩
  let m₀ := BulkOriginData.imaginaryVector q
  let r := BulkPerron.signMul (fun e => T (G.head e)) (fun e => (q e : ℂ))
  let L : ((G.Edge → ℂ) × ℂ) → (G.Edge → ℂ) →L[ℂ] (G.Edge → ℂ) :=
    fun t => Origin.stabilityCLM G.matrix t.1
  let ψ : ((G.Edge → ℂ) × ℂ) → (G.Edge → ℂ) →L[ℂ] ℂ :=
    fun t => vertexFunctional (incidence G) T (vertexValues G t.1 t.2)
  obtain ⟨φ, hnorm, hopen, hleft, hsimple⟩ := BulkOriginData.actual_origin_kernel_data (V := G.Edge)
    external G.matrix (fun _ => 0) 0 q (G.matrix_nonnegative) hconn hq hsol
    (fun e => T (G.head e)) (fun e => hT (G.head e)) (transition_sign_flip G T hflip)
  have hm : BasicEstimates.IsUpperSolution m₀ := by
    intro e
    simpa [m₀, BulkOriginData.imaginaryVector, Complex.mul_im] using hq e
  have hd : ∀ y, (0 : ℂ) + incidence G m₀ y ≠ 0 := by
    intro y
    obtain ⟨e, he⟩ := hdegree y
    have hh := BulkDyson.NB.outgoingSum_im_pos G m₀ hm (G.reverse e)
    simp only [G.reverse_head, he] at hh
    intro hz
    have hz' : incidence G m₀ y = 0 := by simpa using hz
    simpa [← incidence_apply, hz'] using hh
  have hL : ContinuousAt L (m₀, 0) :=
    ((Origin.continuous_stability G.matrix).comp continuous_fst).continuousAt
  have hψ : ContinuousAt ψ (m₀, 0) :=
    (continuous_vertexFunctional (incidence G) T).continuousAt.comp
      (continuousAt_vertexValues G m₀ 0 hd)
  have hopen' : ψ (m₀, 0) r ≠ 0 := vertexFunctional_detects_origin G T q hT hflip hq hdegree
  obtain ⟨A, hA, hev⟩ := Deflation.local_augmented_bound (m₀, (0 : ℂ)) L ψ r hL hψ hopen'
    (fun u hu => ⟨φ u, hsimple u hu⟩)
  refine ⟨A, hA, ?_⟩
  filter_upwards [hev] with t ht
  intro u
  simpa only [L, ψ, Origin.stabilityCLM_apply, InteriorStability.stabilityOperator,
    LinearMap.coe_mk, AddHom.coe_mk, vertexFunctional_apply, vertexValues,
    vertexBalanceLinear] using ht u

theorem actual_vertex_balance_identity (T : V → ℂ) (m g : G.Edge → ℂ) (z : ℂ) :
    vertexBalance (incidence G) T (fun y => z + incidence G m y) (g - m) =
      ∑ y, T y * (vertexValues G g z y - vertexValues G m z y) := by
  unfold vertexBalance vertexValues
  apply Finset.sum_congr rfl
  intro y _
  rw [map_sub, Pi.sub_apply]
  congr 3
  ring

/-- The local bipartite nonlinear estimate with constants chosen uniformly
before the spectral point and the approximate solution. The graph, its actual
origin solution, and the ordinary Perron theorem are the only input data. -/
theorem origin_nonlinear_vertex_balance [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : G.Edge → ℝ) (T : V → ℂ)
    (hconn : Resonance.StronglyConnected (fun e f => 0 < G.matrix e f))
    (hq : ∀ e, 0 < q e)
    (hT : ∀ y, T y ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → T y = -T x)
    (hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y)
    (hsol₀ : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ t : (G.Edge → ℂ) × ℂ in 𝓝 (BulkOriginData.imaginaryVector q, 0),
      ∀ g : G.Edge → ℂ,
      BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) t.2 t.1 →
      ‖g - t.1‖ ≤ c →
      (∀ y, t.2 + incidence G g y ≠ 0) ∧
      ‖g - t.1‖ ≤ C * (‖Model.residual G.matrix (fun _ => 0) t.2 g‖ +
        ‖∑ y, T y * (vertexValues G g t.2 y - vertexValues G t.1 t.2 y)‖) := by
  letI : Nonempty G.Edge := ⟨(hdegree (Classical.arbitrary V)).choose⟩
  let m₀ := BulkOriginData.imaginaryVector q
  obtain ⟨e₀, he₀⟩ := Finite.exists_min q
  let b := q e₀ / 4
  have hb : 0 < b := div_pos (hq e₀) (by norm_num)
  let M := ‖m₀‖ + 1
  let V₀ := ‖vertexValues G m₀ 0‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : 0 ≤ V₀ := by dsimp [V₀]; positivity
  have hm₀ : BasicEstimates.IsUpperSolution m₀ := by
    intro e
    simpa [m₀, BulkOriginData.imaginaryVector, Complex.mul_im] using hq e
  have hd₀ : ∀ y, (0 : ℂ) + incidence G m₀ y ≠ 0 := by
    intro y
    obtain ⟨e, he⟩ := hdegree y
    have hh := BulkDyson.NB.outgoingSum_im_pos G m₀ hm₀ (G.reverse e)
    simp only [G.reverse_head, he] at hh
    intro hz
    have hz' : incidence G m₀ y = 0 := by simpa using hz
    simpa [← incidence_apply, hz'] using hh
  have hTnorm : ∀ y, ‖T y‖ ≤ 1 := by
    intro y
    have hh := congrArg norm (hT y)
    rw [norm_pow, norm_one] at hh
    nlinarith [norm_nonneg (T y)]
  obtain ⟨A, hA, haug⟩ := origin_vertex_augmented_bound G external q T hconn hq hT hflip hdegree hsol₀
  obtain ⟨c, C, hc, hC, hnonlinear⟩ := uniform_nonlinear_balance_radius
    G.matrix (fun _ => 0) (incidence G) T b M V₀ A hb hM hV hA hTnorm
  have hmclose : ∀ᶠ t : (G.Edge → ℂ) × ℂ in 𝓝 (m₀, 0),
      ‖t.1 - m₀‖ < min (q e₀ / 2) 1 := by
    apply ((continuous_fst.sub continuous_const).norm.continuousAt.tendsto).eventually_lt_const
    simp only [sub_self, norm_zero]
    exact lt_min (div_pos (hq e₀) (by norm_num)) zero_lt_one
  have hvbound : ∀ᶠ t : (G.Edge → ℂ) × ℂ in 𝓝 (m₀, 0),
      ‖vertexValues G t.1 t.2‖ ≤ V₀ := by
    exact ((continuousAt_vertexValues G m₀ 0 hd₀).norm.tendsto).eventually_le_const
      (by dsimp [V₀]; linarith)
  have hden : ∀ᶠ t : (G.Edge → ℂ) × ℂ in 𝓝 (m₀, 0),
      ∀ y, t.2 + incidence G t.1 y ≠ 0 := by
    apply eventually_all.mpr
    intro y
    exact (continuous_snd.add ((continuous_apply y).comp
      ((incidence G).continuous.comp continuous_fst))).continuousAt.eventually_ne (hd₀ y)
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [haug, hmclose, hvbound, hden] with t htaug htclose htv htden
  intro g hsol hclose
  have hlower : ∀ e, 2 * b ≤ ‖t.1 e‖ := by
    intro e
    have hnorm : ‖m₀ e‖ = q e := by
      simp [m₀, BulkOriginData.imaginaryVector, norm_mul, abs_of_pos (hq e)]
    have hh := norm_sub_norm_le (m₀ e) (t.1 e)
    rw [norm_sub_rev, hnorm] at hh
    have hu := norm_le_pi_norm (t.1 - m₀) e
    simp only [Pi.sub_apply] at hu
    have hsmall := htclose.trans_le (min_le_left _ _)
    dsimp [b]
    linarith [he₀ e]
  have hupper : ∀ e, ‖t.1 e‖ ≤ M := by
    intro e
    have hh : ‖t.1‖ ≤ ‖t.1 - m₀‖ + ‖m₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (t.1 - m₀) m₀
    have hsmall := htclose.trans_le (min_le_right _ _)
    have hu := norm_le_pi_norm t.1 e
    dsimp [M]
    linarith
  have hvertex : ∀ y, ‖-(t.2 + incidence G t.1 y)⁻¹‖ ≤ V₀ :=
    fun y => (norm_le_pi_norm (vertexValues G t.1 t.2) y).trans htv
  obtain ⟨hgd, hbound⟩ := hnonlinear t.2 t.1 g (fun y => t.2 + incidence G t.1 y)
    hsol hlower hupper htden hvertex htaug hclose
  refine ⟨?_, ?_⟩
  · intro y
    convert hgd y using 1
    rw [map_sub, Pi.sub_apply]
    ring
  · rw [actual_vertex_balance_identity] at hbound
    exact hbound

/-- The quantified local statement for the actual physical branch. Its
boundary limit is the established bulk boundary value; the nonlinear estimate
has no unproved linear or balance assumption. -/
theorem bipartite_nonlinear_balance_near_origin [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : G.Edge → ℝ) (T : V → ℂ) (m : ℂ → G.Edge → ℂ)
    (hconn : Resonance.StronglyConnected (fun e f => 0 < G.matrix e f))
    (hq : ∀ e, 0 < q e)
    (hT : ∀ y, T y ^ 2 = 1)
    (hflip : ∀ x y, G.Adj x y → T y = -T x)
    (hdegree : ∀ y, ∃ e : G.Edge, G.tail e = y)
    (hsol₀ : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) 0
      (BulkOriginData.imaginaryVector q))
    (hlim : Tendsto m (𝓝[{z : ℂ | 0 < z.im}] 0) (𝓝 (BulkOriginData.imaginaryVector q)))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z)) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      ‖z‖ ≤ r → 0 < z.im → ‖g - m z‖ ≤ c →
      (∀ y, z + incidence G g y ≠ 0) ∧
      ‖g - m z‖ ≤ C * (‖Model.residual G.matrix (fun _ => 0) z g‖ +
        ‖∑ y, T y * (vertexValues G g z y - vertexValues G (m z) z y)‖) := by
  obtain ⟨c, C, hc, hC, hev⟩ := origin_nonlinear_vertex_balance G external q T
    hconn hq hT hflip hdegree hsol₀
  have ht : Tendsto (fun z : ℂ => (m z, z)) (𝓝[{z : ℂ | 0 < z.im}] 0)
      (𝓝 (BulkOriginData.imaginaryVector q, 0)) :=
    hlim.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hh := ht.eventually hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨ε / 2, c, C, by positivity, hc, hC, ?_⟩
  intro z g hzn hz hclose
  have hzball : z ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  exact hball ⟨hzball, hz⟩ g (hsol z hz) hclose

end NB
end NonSymmetricDyson.Full.Nonlinear
