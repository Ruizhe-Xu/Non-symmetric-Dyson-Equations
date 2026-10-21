import Dyson.Full.MainLinearBulk
import Dyson.Full.Origin

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.MainLinearBulk
universe u
variable {V : Type u} [Fintype V] [Nonempty V]

/-- Extend a proved local origin rate through the entire compact-energy
vertical strip. The only boundary singularity allowed is the origin. -/
theorem isolated_origin_globalization
    (J : Set ℝ) (hJ : IsCompact J) (S : Matrix V V ℝ) (a : V → ℝ)
    (m : ℂ → V → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution S a z (m z))
    (hboundary : ∀ E ∈ J, E ≠ 0 →
      Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ))))
    (r c₀ C₀ : ℝ) (hr : 0 < r) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hlocal : ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im, ‖z‖ < r →
      c₀/‖z‖ ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C₀/‖z‖) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  let R : ℝ := ‖fun i => ∑ j, S i j‖
  have hR : 0 ≤ R := norm_nonneg _
  have hrow (i : V) : ∑ j, S i j ≤ R :=
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H : ℝ := 1 + 2*R
  have hH : 0 < H := by dsimp [H]; positivity
  let K := boundedStrip J H
  have hK := boundedStrip_compact J hJ H
  have hsub : K ⊆ closedStrip J := fun _ hz => ⟨hz.1,hz.2.1⟩
  let K' : Set ℂ := K ∩ {z | r ≤ ‖z‖}
  have hK' : IsCompact K' := hK.inter_right (isClosed_le continuous_const continuous_norm)
  have hbij : ∀ z ∈ K', Function.Bijective (InteriorStability.stabilityOperator S (m z)) := by
    intro z hz
    by_cases hi : 0 < z.im
    · exact InteriorStability.stability_bijective hS hi (hupper z (hsub hz.1)) (hsol z (hsub hz.1))
    · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.1.2.1
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hi0)
      have hne : z.re ≠ 0 := by
        intro hh
        have hz0 : z = 0 := by simpa [hh] using he
        have hh' := hz.2
        simp [hz0] at hh'
        linarith
      simpa only [← he] using hboundary z.re hz.1.1 hne
  obtain ⟨A,hA,hlow⟩ := BulkCompact.uniform_dyson_bound K' hK' S m
    (hcont.mono fun _ hz => hsub hz.1) hbij
  obtain ⟨M₀,hM₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  let M := max 1 M₀
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmod : ∀ z : ℂ, z.re ∈ J → 0 < z.im → ∀ i, ‖m z i‖ ≤ M := by
    intro z hE hz i
    by_cases hh : z.im ≤ H
    · exact (norm_le_pi_norm _ i).trans ((hM₀ z ⟨hE,hz.le,hh⟩).trans (le_max_right _ _))
    · have hHi : 1 ≤ z.im := by dsimp [H] at hh; linarith
      exact (BasicEstimates.rough_bound hS hz (hupper z ⟨hE,hz.le⟩)
        (hsol z ⟨hE,hz.le⟩) i).trans
          ((inv_le_one₀ hz).mpr hHi |>.trans (le_max_left _ _))
  let d : ℝ := Real.sqrt (Fintype.card V)
  have hd : 0 < d := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  let b := (1/(1+M^2*R))/d
  have hb : 0 < b := by dsimp [b]; positivity
  let c := min c₀ (b / max 1 r⁻¹)
  let C := max C₀ (d * max A 2)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hE hz
  let N := ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz
    (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖
  have hz0 : z ≠ 0 := by intro hh; simp [hh] at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hbN : b ≤ N := by
    have hl := Linear.inverse_norm_lower_bound S a z (m z) hS hz
      (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) M R hM.le hR (hmod z hE hz) hrow
    have he := EuclideanInverse.conjugate_norm_lower
      (InteriorStability.stabilityContinuousEquiv hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)).symm.toContinuousLinearMap
    exact (div_le_iff₀ hd).mpr ((hl.trans he).trans_eq (mul_comm _ _))
  have hcb : c ≤ b := (min_le_right _ _).trans (div_le_self hb.le (le_max_left _ _))
  have hscale : 1 ≤ max (1 : ℝ) ‖z‖⁻¹ := le_max_left _ _
  constructor
  · by_cases hnear : ‖z‖ < r
    · rw [mul_max_of_nonneg 1 ‖z‖⁻¹ hc.le, mul_one]
      apply max_le (hcb.trans hbN)
      have hl := (hlocal z hE hz hnear).1
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (inv_nonneg.mpr hzn.le)).trans
        (by simpa [div_eq_mul_inv] using hl)
    · have hweight : max 1 ‖z‖⁻¹ ≤ max 1 r⁻¹ :=
        max_le_max le_rfl (inv_le_inv₀ hzn hr |>.mpr (le_of_not_gt hnear))
      have hcm : c * max 1 r⁻¹ ≤ b := by
        apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mp
        exact min_le_right _ _
      exact ((mul_le_mul_of_nonneg_left hweight hc.le).trans hcm).trans hbN
  · by_cases hnear : ‖z‖ < r
    · exact (hlocal z hE hz hnear).2.trans (by
        change C₀/‖z‖ ≤ C*max 1 ‖z‖⁻¹
        rw [div_eq_mul_inv]
        exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (by positivity) hC.le)
    · have hbound : ∀ x, ‖x‖ ≤ max A 2 * ‖InteriorStability.stabilityOperator S (m z) x‖ := by
        intro x
        by_cases hh : z.im ≤ H
        · exact (hlow z ⟨⟨hE,hz.le,hh⟩,le_of_not_gt hnear⟩ x).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        · have hs : ∀ i, 2*∑ j, S i j ≤ z.im^2 := by
            intro i
            have hHsq : 2*R ≤ H^2 := by dsimp [H]; nlinarith
            nlinarith [hrow i, lt_of_not_ge hh]
          exact (Linear.high_height_lower_norm_bound S a z (m z) hS hz
            (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) hs x).trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
      have hu := EuclideanInverse.stability_inverse_upper S a z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩) (max A 2) (by positivity) hbound
      exact (hu.trans (le_max_right C₀ _)).trans (le_mul_of_one_le_right hC.le hscale)

theorem origin_full_strip_from_model
    (J : Set ℝ) (hJ : IsCompact J) (S : Matrix V V ℝ) 
    (m : ℂ → V → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hboundary : ∀ E ∈ J, E ≠ 0 →
      Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ))))
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : V → ℝ) (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i)
    (hupperAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsolAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hlim : Filter.Tendsto m (nhdsWithin (0 : ℂ) {z : ℂ | 0 < z.im})
      (nhds (BulkOriginData.imaginaryVector q))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  obtain ⟨r,c,C,hr,hc',hC,hlocal⟩ := Origin.bipartite_origin_family_inverse (V := V)
    external S q m hS hc hq hsol₀ t ht hs hupperAll hsolAll hlim
  exact isolated_origin_globalization J hJ S (fun _ => 0) m hS hcont hupper hsol hboundary
    r c C hr hc' hC (fun z _ hz hzr => hlocal z hz hzr)

theorem symmetric_origin_full_strip
    (J : Set ℝ) (hJ : IsCompact J) (S : Matrix V V ℝ) 
    (m : ℂ → V → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : V → ℝ) (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i)
    (hupperAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsolAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hlim : Filter.Tendsto m (nhdsWithin (0 : ℂ) {z : ℂ | 0 < z.im})
      (nhds (BulkOriginData.imaginaryVector q))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  have hconn : Resonance.StronglyConnected (fun i j => S i j ≠ 0) := by
    have he : (fun i j => 0 < S i j) = (fun i j => S i j ≠ 0) := by
      funext i j
      exact propext (lt_iff_le_and_ne.trans (by simp [hS i j, ne_comm]))
    rwa [← he]
  have hboundary : ∀ E ∈ J, E ≠ 0 →
      Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ))) := by
    intro E hE hEn
    apply BulkBoundary.symmetric_boundary_bijective S (fun _ => 0) E (m (E : ℂ))
      hS hconn hsymm (hupper _ ⟨by simpa using hE, by simp⟩)
      (hsol _ ⟨by simpa using hE, by simp⟩)
    rintro ⟨ha,_⟩
    exact hEn (ha (Classical.arbitrary V)).symm
  exact origin_full_strip_from_model J hJ S m hS hcont hupper hsol hboundary external
    q hc hq hsol₀ t ht hs hupperAll hsolAll hlim

theorem NB.origin_full_strip
    (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (J : Set ℝ) (hJ : IsCompact J) 
    (m : ℂ → G.Edge → ℂ)
    (hcont : ContinuousOn m (closedStrip J))
    (hupper : ∀ z ∈ closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ closedStrip J, BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (q : G.Edge → ℝ)
    (hq : ∀ i, 0 < q i)
    (hsol₀ : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) 0 (BulkOriginData.imaginaryVector q))
    (t : G.Edge → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, G.matrix i j ≠ 0 → t j = -t i)
    (hupperAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsolAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) z (m z))
    (hlim : Filter.Tendsto m (nhdsWithin (0 : ℂ) {z : ℂ | 0 < z.im})
      (nhds (BulkOriginData.imaginaryVector q))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, ∀ hE : z.re ∈ J, ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => 0) z (m z) G.matrix_nonnegative hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ∧
      ‖EuclideanInverse.stabilityInverse G.matrix (fun _ => 0) z (m z) G.matrix_nonnegative hz
        (hupper z ⟨hE,hz.le⟩) (hsol z ⟨hE,hz.le⟩)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  classical
  letI : Nonempty G.Edge := ⟨root⟩
  have hconn : Resonance.StronglyConnected (fun i j => 0 < G.matrix i j) := by
    have he : (fun i j => 0 < G.matrix i j) = G.CanFollow := by
      funext i j
      exact propext (by
        by_cases h : G.CanFollow i j <;>
          simp [Nonbacktracking.BaseGraph.matrix, h])
    rw [he]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  have hboundary : ∀ E ∈ J, E ≠ 0 →
      Function.Bijective (InteriorStability.stabilityOperator G.matrix (m (E : ℂ))) := by
    intro E hE hEn
    apply BulkBoundary.NB.boundary_bijective G (fun _ => 0) E (m (E : ℂ)) hd root hbase
      (hupper _ ⟨by simpa using hE, by simp⟩) (hsol _ ⟨by simpa using hE, by simp⟩)
    rintro ⟨ha,_⟩
    exact hEn (ha (G.head root)).symm
  exact origin_full_strip_from_model J hJ G.matrix m G.matrix_nonnegative hcont hupper hsol hboundary
    external q hconn hq hsol₀ t ht hs hupperAll hsolAll hlim

end NonSymmetricDyson.Full.MainLinearBulk
