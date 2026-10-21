import Dyson.Full.SpectralShift
import Dyson.Full.NonlinearNB
import Dyson.Full.BoundaryLocalLimits

/-! Closure of the exceptional model hypotheses: canonical boundary values
give the imaginary origin vector, and a set bipartition gives the signs. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace NonSymmetricDyson.Full.Exceptional
universe u
variable {V : Type u} [Fintype V]

def partitionSign (part : Set V) (x : V) : ℂ := by
  classical
  exact if x ∈ part then 1 else -1

theorem partitionSign_square (part : Set V) (x : V) : partitionSign part x ^ 2 = 1 := by
  classical
  by_cases hx : x ∈ part <;> simp [partitionSign, hx]

theorem partitionSign_flip {E : V → V → Prop} (part : Set V)
    (hp : BulkGraph.IsBipartition (E := E) part) {x y : V} (hxy : E x y) :
    partitionSign part y = -partitionSign part x := by
  classical
  have hh := hp x y hxy
  by_cases hx : x ∈ part
  · have hy : y ∉ part := hh.mp hx
    simp [partitionSign, hx, hy]
  · have hy : y ∈ part := by by_contra hn; exact hx (hh.mpr hn)
    simp [partitionSign, hx, hy]

theorem canonical_closed_strip_data
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (J : Set ℝ) (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) :
    ContinuousOn (Boundary.boundaryVector m) (MainLinearBulk.closedStrip J) ∧
    (∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m z)) ∧
    ∀ z ∈ MainLinearBulk.closedStrip J,
      BasicEstimates.IsDysonSolution S a z (Boundary.boundaryVector m z) := by
  have hsub : MainLinearBulk.closedStrip J ⊆ Boundary.commonRegularDomain m := by
    intro z hz
    rcases lt_or_eq_of_le hz.2 with hi | hi
    · exact Or.inl hi
    · refine Or.inr ⟨z.re, hregular _ hz.1, ?_⟩
      exact Complex.ext (by simp) (by simpa using hi)
  refine ⟨(Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq).mono hsub, ?_, ?_⟩
  · intro z hz
    by_cases hi : 0 < z.im
    · rw [Boundary.family_extension_agrees S a hS m hupper heq z hi]
      exact hupper z hi
    · have him : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
      simpa only [← he] using hbulk z.re hz.1
  · intro z hz
    by_cases hi : 0 < z.im
    · rw [Boundary.family_extension_agrees S a hS m hupper heq z hi]
      exact heq z hi
    · have him : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
      simpa only [← he] using (Boundary.family_boundary_equation algebraic puiseux S a hS m
        hupper heq z.re (hregular _ hz.1)).2.2

/-- At a regular zero-energy bulk point, the imaginary origin vector and
its full upper-half-plane limit are consequences of the actual model. -/
theorem canonical_origin_data
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j) (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hregular : (0 : ℝ) ∉ Boundary.singularUnion m)
    (hbulk : BasicEstimates.IsUpperSolution (Boundary.boundaryVector m 0)) :
    let q : V → ℝ := fun i => (Boundary.boundaryVector m 0 i).im
    (∀ i, 0 < q i) ∧
    Boundary.boundaryVector m 0 = BulkOriginData.imaginaryVector q ∧
    BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q) ∧
    Tendsto m (𝓝[ExternalAlgebraic.upper] 0) (𝓝 (BulkOriginData.imaginaryVector q)) ∧
    Tendsto (Boundary.boundaryVector m) (𝓝[ExternalAlgebraic.upper] 0)
      (𝓝 (BulkOriginData.imaginaryVector q)) := by
  dsimp only
  have hvert := Boundary.family_boundary_limits algebraic puiseux S (fun _ => 0) hS m hupper heq 0 hregular
  have him := Origin.imaginary_boundary_of_limit S (fun η : ℝ => m ((η : ℂ) * Complex.I))
    (Boundary.boundaryVector m 0) hS
    (fun η hη => hupper _ (by simpa using hη))
    (fun η hη => heq _ (by simpa using hη))
    (by simpa [Boundary.IsBoundaryValue] using hvert)
  have hcont := Boundary.family_boundary_continuous algebraic puiseux S (fun _ => 0) hS m hupper heq
    0 (Or.inr ⟨0, hregular, by simp⟩)
  have hlimM := (hcont.mono (show ExternalAlgebraic.upper ⊆ Boundary.commonRegularDomain m
    from fun _ hz => Or.inl hz)).tendsto
  have hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] 0) (𝓝 (Boundary.boundaryVector m 0)) := by
    apply hlimM.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hz
  refine ⟨hbulk, him, ?_, ?_, ?_⟩
  · rw [← him]
    simpa using (Boundary.family_boundary_equation algebraic puiseux S (fun _ => 0) hS m
      hupper heq 0 hregular).2.2
  · rw [← him]
    exact hlim
  · rw [← him]
    exact hlimM

/-- Away from zero, compactness makes the exceptional weight uniformly
bounded, so ordinary stability already has the claimed weighted form. -/
theorem weighted_bound_of_zero_not_mem
    (J : Set ℝ) (hJ : IsCompact J) (hzero : (0 : ℝ) ∉ J)
    (N : ℂ → ℝ) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hbound : ∀ z : ℂ, z.re ∈ J → 0 < z.im → c ≤ N z ∧ N z ≤ C) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ z : ℂ, z.re ∈ J → 0 < z.im →
      c' * max 1 ‖z‖⁻¹ ≤ N z ∧ N z ≤ C' * max 1 ‖z‖⁻¹ := by
  by_cases hne : J.Nonempty
  · obtain ⟨E₀, hE₀, hmin⟩ := hJ.exists_isMinOn hne (continuous_abs.continuousOn)
    have hδ : 0 < |E₀| := abs_pos.mpr (by intro h; exact hzero (h ▸ hE₀))
    let W := max 1 |E₀|⁻¹
    have hW : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨c / W, C, div_pos hc hW, hC, ?_⟩
    intro z hE hz
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le hz (Complex.im_le_norm z)
    have hlow : |E₀| ≤ ‖z‖ := (hmin hE).trans (Complex.abs_re_le_norm z)
    have hw : max 1 ‖z‖⁻¹ ≤ W := max_le_max le_rfl (inv_anti₀ hδ hlow)
    refine ⟨?_, ?_⟩
    · calc
        c / W * max 1 ‖z‖⁻¹ ≤ c / W * W := mul_le_mul_of_nonneg_left hw (by positivity)
        _ = c := div_mul_cancel₀ _ hW.ne'
        _ ≤ N z := (hbound z hE hz).1
    · exact (hbound z hE hz).2.trans (le_mul_of_one_le_right hC.le (le_max_left _ _))
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro z hE
    exact False.elim (hne ⟨z.re, hE⟩)

/-- A canonical-boundary closure lemma.  In particular, a compact energy set
need not contain the exceptional energy. -/
theorem canonical_exceptional_strip [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ)))
    (hboundary : ∀ E ∈ J, E ≠ 0 → Function.Bijective
      (InteriorStability.stabilityOperator S (Boundary.boundaryVector m (E : ℂ))))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  classical
  obtain ⟨hcont, hu, he⟩ := canonical_closed_strip_data algebraic puiseux S (fun _ => 0)
    hS m hupper heq J hregular hbulk
  have huAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (Boundary.boundaryVector m z) := by
    intro z hz
    rw [Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hz]
    exact hupper z hz
  have heAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z
      (Boundary.boundaryVector m z) := by
    intro z hz
    rw [Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hz]
    exact heq z hz
  by_cases hzero : (0 : ℝ) ∈ J
  · obtain ⟨hq, _, hsol₀, _, hlim⟩ := canonical_origin_data algebraic puiseux S hS m
      hupper heq (hregular 0 hzero) (by simpa using hbulk 0 hzero)
    obtain ⟨c, C, hc', hC, hb⟩ := MainLinearBulk.origin_full_strip_from_model J hJ S
      (Boundary.boundaryVector m) hS hcont hu he hboundary external _ hc hq hsol₀
      t ht hs huAll heAll hlim
    refine ⟨c, C, hc', hC, ?_⟩
    intro z hzJ hz
    have hh := hb z hzJ hz
    simpa only [Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hz] using hh
  · have hbij : ∀ E ∈ J, Function.Bijective
        (InteriorStability.stabilityOperator S (Boundary.boundaryVector m (E : ℂ))) := by
      intro E hE
      exact hboundary E hE (by intro he0; exact hzero (he0 ▸ hE))
    obtain ⟨c, C, hc', hC, hb⟩ := MainLinearBulk.full_strip_inverse_bounds J hJ S (fun _ => 0)
      (Boundary.boundaryVector m) hS hcont hu he hbij
    let N : ℂ → ℝ := fun z => if hz : 0 < z.im then
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz (hupper z hz) (heq z hz)‖ else 0
    have hN : ∀ z : ℂ, z.re ∈ J → 0 < z.im → c ≤ N z ∧ N z ≤ C := by
      intro z hzJ hz
      have hh := hb z hzJ hz
      simpa only [N, dif_pos hz,
        Boundary.family_extension_agrees S (fun _ => 0) hS m hupper heq z hz] using hh
    obtain ⟨c', C', hc'', hC', hh⟩ := weighted_bound_of_zero_not_mem J hJ hzero N c C hc' hC hN
    refine ⟨c', C', hc'', hC', ?_⟩
    intro z hzJ hz
    simpa only [N, dif_pos hz] using hh z hzJ hz

/-- The symmetric-support exceptional theorem, with signs and the origin
boundary vector derived from the actual model. -/
theorem symmetric_exceptional_strip [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)
    (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  have hconn : Resonance.StronglyConnected (fun i j => S i j ≠ 0) := by
    have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
      funext i j
      exact propext (lt_iff_le_and_ne.trans (by simp [hS i j, ne_comm]))
    rwa [← he]
  apply canonical_exceptional_strip algebraic puiseux external S hS hc m hupper heq J hJ hregular hbulk
    ?_ (partitionSign part) (partitionSign_square part) (fun _ _ h => partitionSign_flip part hp h)
  intro E hE hEn
  apply BulkBoundary.symmetric_boundary_bijective S (fun _ => 0) E
    (Boundary.boundaryVector m (E : ℂ)) hS hconn hsymm (hbulk E hE)
    (Boundary.family_boundary_equation algebraic puiseux S (fun _ => 0) hS m hupper heq E
      (hregular E hE)).2.2
  rintro ⟨ha, _⟩
  exact hEn (ha (Classical.arbitrary V)).symm

namespace NB

/-- Actual non-backtracking M6 exceptional case.  Neither the imaginary
boundary vector nor an alternating edge eigenvector is an input. -/
theorem exceptional_strip
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => 0) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => 0) z (m z)
        G.matrix_nonnegative hz (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  classical
  letI : Nonempty G.Edge := ⟨root⟩
  have hconn : Resonance.StronglyConnected (fun i j => 0 < G.matrix i j) := by
    have he : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
      funext i j
      exact propext (by by_cases h : G.CanFollow i j <;> simp [Nonbacktracking.BaseGraph.matrix, h])
    rw [he]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  apply canonical_exceptional_strip algebraic puiseux external G.matrix G.matrix_nonnegative hconn
    m hupper heq J hJ hregular hbulk ?_ (fun e => partitionSign part (G.head e))
    (fun e => partitionSign_square part (G.head e))
    (Nonlinear.NB.transition_sign_flip G _ (fun _ _ h => partitionSign_flip part hp h))
  intro E hE hEn
  apply BulkBoundary.NB.boundary_bijective G (fun _ => 0) E (Boundary.boundaryVector m (E : ℂ))
    hd root hbase (hbulk E hE)
    (Boundary.family_boundary_equation algebraic puiseux G.matrix (fun _ => 0)
      G.matrix_nonnegative m hupper heq E (hregular E hE)).2.2
  rintro ⟨ha, _⟩
  exact hEn (ha (G.head root)).symm

/-- M7(ii) for the actual canonical bulk origin: its boundary vector,
Perron simplicity, and balance detection are all derived internally. -/
theorem main_theorem_seven_balance [Nonempty V]
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge]
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := G.Adj) part)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
    (hregular : (0 : ℝ) ∉ Boundary.singularUnion m)
    (hbulk : BasicEstimates.IsUpperSolution (Boundary.boundaryVector m 0)) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      ‖z‖ ≤ r → 0 < z.im → ‖g - m z‖ ≤ c →
      (∀ y, z + Nonlinear.NB.incidence G g y ≠ 0) ∧
      ‖g - m z‖ ≤ C * (‖Model.residual G.matrix (fun _ => 0) z g‖ +
        ‖∑ y, partitionSign part y * (Nonlinear.NB.vertexValues G g z y -
          Nonlinear.NB.vertexValues G (m z) z y)‖) := by
  classical
  obtain ⟨hq, _, hsol₀, hlim, _⟩ := canonical_origin_data algebraic puiseux G.matrix
    G.matrix_nonnegative m hupper heq hregular hbulk
  have hconn : Resonance.StronglyConnected (fun i j => 0 < G.matrix i j) := by
    have he : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
      funext i j
      exact propext (by by_cases h : G.CanFollow i j <;> simp [Nonbacktracking.BaseGraph.matrix, h])
    rw [he]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  apply Nonlinear.NB.bipartite_nonlinear_balance_near_origin G external _ (partitionSign part) m
    hconn hq (partitionSign_square part) (fun _ _ h => partitionSign_flip part hp h) ?_ hsol₀ hlim heq
  intro y
  obtain ⟨x, hxy, _, _⟩ := hd y y y
  exact ⟨⟨(y, x), hxy⟩, rfl⟩

end NB
end NonSymmetricDyson.Full.Exceptional
