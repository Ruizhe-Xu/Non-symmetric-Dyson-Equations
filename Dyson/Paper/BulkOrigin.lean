import Dyson.Paper.BulkStability
import Dyson.Full.MainLinearExceptional
import Dyson.Full.BulkOriginData
import Dyson.Full.Origin

/-! `prop.bipartite-origin-instability`, including the nonzero real boundary
points in the manuscript's closed half-disc N_ε(0). The simple kernel,
nonzero left pairing, and opening identity are derived from actual matrices. -/
noncomputable section
open scoped Topology BigOperators Classical
open Filter Set
namespace NonSymmetricDyson.Paper.BulkOrigin
open Full Resonance
universe u
variable {V : Type u} [Fintype V]

/-- The original exact identity (I−m²S)Tm=−zTm². -/
theorem bad_vector_linear_opening (S : Matrix V V ℝ) (t m : V → ℂ) (z : ℂ)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) (hm : ∀ i, m i ≠ 0)
    (heq : BasicEstimates.IsDysonSolution S (fun _ => 0) z m) :
    InteriorStability.stabilityOperator S m (fun i => t i*m i) =
      fun i => -z*t i*m i^2 :=
  Full.BulkAlgebra.bipartite_direction_identity S t m z hs hm
    (fun i => by simpa [Model.action_apply] using heq i)

/-- Uniform inverse bounds for all nearby nonzero spectral points, without
an Im z>0 restriction. This is the fixed-complement/left-kernel argument. -/
theorem nearby_origin_inverse [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (q : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => 0 < S i j)) (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i^2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ m in 𝓝 (BulkOriginData.imaginaryVector q),
      ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 → (∀ i, m i ≠ 0) →
      BasicEstimates.IsDysonSolution S (fun _ => 0) z m →
      ∃ e : (V → ℂ) ≃L[ℂ] (V → ℂ),
        (∀ x, e x = InteriorStability.stabilityOperator S m x) ∧
        c/‖z‖ ≤ ‖EuclideanInverse.inverse e‖ ∧ ‖EuclideanInverse.inverse e‖ ≤ C/‖z‖ := by
  let m₀ := BulkOriginData.imaginaryVector q
  let v₀ := Origin.openingVector t m₀
  let b₀ := Origin.openingRight t m₀
  have hv₀ : v₀ ≠ 0 := by
    intro hz
    let i : V := Classical.arbitrary V
    have hti : t i ≠ 0 := by intro hi; have hh := ht i; simp [hi] at hh
    have hh := congrFun hz i
    rw [show v₀ = BulkPerron.signMul t (fun i => (q i : ℂ)) from Origin.openingVector_origin t q] at hh
    exact mul_ne_zero hti (Complex.ofReal_ne_zero.mpr (hq i).ne') hh
  let A := ‖v₀‖/2
  let B := Real.sqrt (Fintype.card V) * (1+‖b₀‖)
  have hd : 0 < Real.sqrt (Fintype.card V) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hA : 0 < A := half_pos (norm_pos_iff.mpr hv₀)
  have hB : 0 < B := by dsimp [B]; positivity
  have hv : Continuous (Origin.openingVector t) := by
    apply continuous_pi; intro i; dsimp [Origin.openingVector]; fun_prop
  have hb : Continuous (Origin.openingRight t) := by
    apply continuous_pi; intro i; dsimp [Origin.openingRight]; fun_prop
  have hev : ∀ᶠ m in 𝓝 m₀, A ≤ ‖Origin.openingVector t m‖ :=
    hv.continuousAt.norm.tendsto.eventually_const_le (by dsimp [A,v₀]; linarith [norm_pos_iff.mpr hv₀])
  have heb : ∀ᶠ m in 𝓝 m₀, ‖Origin.openingRight t m‖ ≤ 1+‖b₀‖ :=
    hb.continuousAt.norm.tendsto.eventually_le_const (by dsimp [b₀]; linarith)
  obtain ⟨C,hC,hevC⟩ := Origin.bipartite_origin_bound external S q hS hc hq hsol₀ t ht hs
  refine ⟨A/B,Real.sqrt (Fintype.card V)*C,div_pos hA hB,mul_pos hd hC,?_⟩
  filter_upwards [hev,heb,hevC] with m hvm hbm hCm
  intro z hz hzle hm heq
  have hlow := hCm z hz hzle hm heq
  have hinj : Function.Injective (InteriorStability.stabilityOperator S m) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh := hlow x
    rw [hx,norm_zero,mul_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  let e : (V → ℂ) ≃L[ℂ] (V → ℂ) :=
    (LinearEquiv.ofBijective (InteriorStability.stabilityOperator S m)
      ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  refine ⟨e,fun _ => rfl,?_,?_⟩
  · apply EuclideanInverse.inverse_uniform_lower_of_identity e
      (Origin.openingVector t m) (Origin.openingRight t m) z hz A B hA hB
    · exact hvm.trans (Norms.sup_le_euclidean _)
    · exact (Norms.euclidean_le_sqrt_card_mul_sup _).trans
        (mul_le_mul_of_nonneg_left hbm hd.le)
    · exact Origin.opening_identity S t m z hs hm heq
  · have hh := EuclideanInverse.inverse_upper_of_sup_lower e (C/‖z‖) (by positivity) hlow
    convert hh using 1 <;> ring

/-- Local boundedness at zero produces the positive imaginary origin value;
no bulk positivity, finite boundary value, or limiting vector is assumed. -/
theorem bounded_origin_data
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → V → ℂ)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (ε M : ℝ) (hε : 0 < ε)
    (hbound : ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ ε → ∀ i, ‖m z i‖ ≤ M) :
    ∃ q : V → ℝ, (∀ i, 0 < q i) ∧
      Boundary.boundaryVector m 0 = BulkOriginData.imaginaryVector q ∧
      BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q) ∧
      Tendsto (Boundary.boundaryVector m) (𝓝[ExternalAlgebraic.closedUpper] 0)
        (𝓝 (BulkOriginData.imaginaryVector q)) ∧
      ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (0 : ℂ),
        (∀ i, Boundary.boundaryVector m z i ≠ 0) ∧
        BasicEstimates.IsDysonSolution S (fun _ => 0) z (Boundary.boundaryVector m z) := by
  have hregular : (0 : ℝ) ∉ Boundary.singularUnion m := by
    intro hs
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hs
    apply Boundary.not_singular_of_bounded (M := max M ε⁻¹) _ hi
    intro η hη
    by_cases hsmall : η ≤ ε
    · apply (hbound (Foundations.vertical 0 η) (by simpa using hη) _ i).trans (le_max_left _ _)
      simpa [Foundations.vertical,norm_mul,Complex.norm_real,abs_of_pos hη] using hsmall
    · have hrec : η⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hη hε).mpr (le_of_not_ge hsmall)
      have hh := BasicEstimates.rough_bound hS (by simpa using hη)
        (hupper (Foundations.vertical 0 η) (by simpa using hη)) (heq _ (by simpa using hη)) i
      exact hh.trans (by simpa using hrec.trans (le_max_right M ε⁻¹))
  have hb := Boundary.family_boundary_equation algebraic puiseux S (fun _ => 0) hS m hupper heq 0 hregular
  have hvert := Boundary.family_boundary_limits algebraic puiseux S (fun _ => 0) hS m hupper heq 0 hregular
  have him := Origin.imaginary_boundary_of_limit S (fun η : ℝ => m ((η : ℂ)*Complex.I))
    (Boundary.boundaryVector m 0) hS (fun η hη => hupper _ (by simpa using hη))
    (fun η hη => heq _ (by simpa using hη)) (by simpa [Boundary.IsBoundaryValue] using hvert)
  simp only [Complex.ofReal_zero] at hb hvert
  let q : V → ℝ := fun i => (Boundary.boundaryVector m 0 i).im
  have himq : Boundary.boundaryVector m 0 = BulkOriginData.imaginaryVector q := him
  have hq (i : V) : 0 < q i := by
    apply lt_of_le_of_ne (hb.2.1 i)
    intro hz
    apply hb.1 i
    rw [himq]
    simp [BulkOriginData.imaginaryVector,q,hz.symm]
  have hreal : ∀ᶠ z : ℂ in 𝓝 0, z.re ∉ Boundary.singularUnion m :=
    (Complex.continuous_re.continuousAt (x := 0)).tendsto.eventually
      (by simpa using (Boundary.family_singular_finite algebraic puiseux S (fun _ => 0) hS m hupper heq).isClosed.isOpen_compl.mem_nhds hregular)
  have hdomain : ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (0 : ℂ), z ∈ Boundary.commonRegularDomain m := by
    filter_upwards [hreal.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hi
    rcases lt_or_eq_of_le hi with hp | he
    · exact Or.inl hp
    · refine Or.inr ⟨z.re,hz,?_⟩
      exact Complex.ext (by simp) (by simpa using he)
  have hcont := Boundary.family_boundary_continuous algebraic puiseux S (fun _ => 0) hS m hupper heq
    0 (Or.inr ⟨0,hregular,by simp⟩)
  have hlim := (hcont.mono_of_mem_nhdsWithin hdomain).tendsto
  refine ⟨q,hq,himq,?_,?_,?_⟩
  · simpa only [←himq] using hb.2.2
  · simpa only [←himq] using hlim
  · filter_upwards [hdomain] with z hz
    rcases hz with hp | ⟨E,hE,rfl⟩
    · rw [Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hp]
      exact ⟨BasicEstimates.component_ne_zero (hupper z hp),heq z hp⟩
    · have hh := Boundary.family_boundary_equation algebraic puiseux S (fun _ => 0) hS m hupper heq E hE
      exact ⟨hh.1,hh.2.2⟩

/-- Closed-half-disc form of the origin estimate, assembled only from
boundedness, the actual equation, and the period-two support structure. -/
theorem origin_instability_from_period_two [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : StronglyConnected (fun i j => 0 < S i j))
    (t : V → ℂ) (ht : ∀ i, t i^2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i)
    (ε M : ℝ) (hε : 0 < ε)
    (hbound : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ ε → ∀ i,
      ‖Boundary.boundaryVector (GlobalWellPosedness.solution S (fun _ => 0) hS) z i‖ ≤ M) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ ε ∧ 0 < c ∧ 0 < C ∧
      ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ r → z ≠ 0 →
      ∃ e : (V → ℂ) ≃L[ℂ] (V → ℂ),
        (∀ x, e x = InteriorStability.stabilityOperator S
          (Boundary.boundaryVector (GlobalWellPosedness.solution S (fun _ => 0) hS) z) x) ∧
        c/‖z‖ ≤ ‖EuclideanInverse.inverse e‖ ∧ ‖EuclideanInverse.inverse e‖ ≤ C/‖z‖ := by
  let m := GlobalWellPosedness.solution S (fun _ => 0) hS
  have hm := fun z hz => GlobalWellPosedness.solution_upper (fun _ => 0) hS (z := z) hz
  have heq := fun z hz => GlobalWellPosedness.solution_equation (fun _ => 0) hS (z := z) hz
  have hmod : ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ ε → ∀ i, ‖m z i‖ ≤ M := by
    intro z hz hzN i
    have hh := hbound z hz.le hzN i
    change ‖Boundary.boundaryVector m z i‖ ≤ M at hh
    rwa [Boundary.family_extension_agrees S (fun _ => 0) hS m hm heq z hz] at hh
  obtain ⟨q,hq,hm₀,heq₀,hlim,hlocal⟩ := bounded_origin_data algebraic puiseux S hS m hm heq ε M hε hmod
  obtain ⟨c,C,hc',hC,hnear⟩ := nearby_origin_inverse external S q hS hc hq heq₀ t ht hs
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhdsWithin_iff.mp ((hlim.eventually hnear).and hlocal)
  let r := min ε (min (d/2) 1)
  have hr : 0 < r := lt_min hε (lt_min (half_pos hd) zero_lt_one)
  refine ⟨r,c,C,hr,min_le_left _ _,hc',hC,?_⟩
  intro z hz hzN hz0
  have hzd : ‖z‖ < d := lt_of_le_of_lt (hzN.trans ((min_le_right ε _).trans (min_le_left _ _))) (by linarith)
  have hh := hball ⟨by simpa [Metric.mem_ball,dist_zero_right] using hzd,hz⟩
  exact hh.1 z hz0 (hzN.trans ((min_le_right ε _).trans (min_le_right _ _))) hh.2.1 hh.2.2

/-- `prop.bipartite-origin-instability`, symmetric case, with precisely the
original structural assumptions and the entire closed upper half-disc. -/
theorem symmetric_origin {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{0})
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (_hsym : ∀ i j, S i j = S j i)
    (part : Set (Fin n)) (hp : Full.BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (ε M : ℝ) (hε : 0 < ε)
    (hbound : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ ε → ∀ i,
      ‖Boundary.boundaryVector (GlobalWellPosedness.solution S (fun _ => 0) hS) z i‖ ≤ M) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ ε ∧ 0 < c ∧ 0 < C ∧
      ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ r → z ≠ 0 →
      ∃ e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
        (∀ x, e x = InteriorStability.stabilityOperator S
          (Boundary.boundaryVector (GlobalWellPosedness.solution S (fun _ => 0) hS) z) x) ∧
        c/‖z‖ ≤ ‖EuclideanInverse.inverse e‖ ∧ ‖EuclideanInverse.inverse e‖ ≤ C/‖z‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact origin_instability_from_period_two algebraic puiseux external S hS
    (Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr)
    (Exceptional.partitionSign part) (Exceptional.partitionSign_square part)
    (fun _ _ h => Exceptional.partitionSign_flip part hp h) ε M hε hbound

namespace NB
variable (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]

theorem origin (root : G.Edge)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (hd : ∀ y, 3 ≤ Full.BulkGraph.NB.degree G y) (hbase : StronglyConnected G.Adj)
    (part : Set V) (hp : Full.BulkGraph.IsBipartition (E := G.Adj) part)
    (ε M : ℝ) (hε : 0 < ε)
    (hbound : ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ ε → ∀ e,
      ‖Boundary.boundaryVector (GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative) z e‖ ≤ M) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ ε ∧ 0 < c ∧ 0 < C ∧
      ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ r → z ≠ 0 →
      ∃ e : (G.Edge → ℂ) ≃L[ℂ] (G.Edge → ℂ),
        (∀ x, e x = InteriorStability.stabilityOperator G.matrix
          (Boundary.boundaryVector (GlobalWellPosedness.solution G.matrix (fun _ => 0) G.matrix_nonnegative) z) x) ∧
        c/‖z‖ ≤ ‖EuclideanInverse.inverse e‖ ∧ ‖EuclideanInverse.inverse e‖ ≤ C/‖z‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  have hc : StronglyConnected (fun e f => 0 < G.matrix e f) := by
    have he : (fun e f => 0 < G.matrix e f) = G.CanFollow := by
      funext e f
      exact propext (by by_cases h : G.CanFollow e f <;> simp [Nonbacktracking.BaseGraph.matrix,h])
    rw [he]
    exact Paper.BulkGraph.NB.strongly_connected G hd hbase
  exact origin_instability_from_period_two algebraic puiseux external G.matrix G.matrix_nonnegative hc
    (fun e => Exceptional.partitionSign part (G.head e))
    (fun e => Exceptional.partitionSign_square part (G.head e))
    (Nonlinear.NB.transition_sign_flip G _ (fun _ _ h => Exceptional.partitionSign_flip part hp h))
    ε M hε hbound

end NB
end NonSymmetricDyson.Paper.BulkOrigin
