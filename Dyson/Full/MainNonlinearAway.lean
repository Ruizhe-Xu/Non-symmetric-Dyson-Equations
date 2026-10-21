import Dyson.Full.MainLinearExceptional
import Dyson.Full.NonlinearStable

/-! Stable nonlinear estimates away from the exceptional spectral point in
complex distance, including vertical points above that real energy. -/
noncomputable section
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.Nonlinear
variable {ι : Type*} [Fintype ι]

theorem stable_region_nonlinear_of_bounds
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (J : Set ℝ) (P : ℂ → Prop) (m : ℂ → ι → ℂ)
    (T s A M : ℝ) (hT : 0 ≤ T) (hs : 0 ≤ s) (hA : 0 < A) (hM : 0 ≤ M)
    (hS : ∀ i j, 0 ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ s)
    (hJ : ∀ E ∈ J, |E| ≤ T)
    (hupper : ∀ z : ℂ, z.re ∈ J → 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, z.re ∈ J → 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (hmod : ∀ z : ℂ, z.re ∈ J → 0 < z.im → z.im ≤ 2 * (s + 1) → ∀ i, ‖m z i‖ ≤ M)
    (hlinear : ∀ z : ℂ, z.re ∈ J → P z → 0 < z.im → z.im ≤ 2 * (s + 1) →
      ∀ u, ‖u‖ ≤ A * ‖InteriorStability.stabilityOperator S (m z) u‖) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : ι → ℂ),
      z.re ∈ J → P z → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual S a z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual S a z g‖ := by
  let H := 2 * (s + 1)
  have hH : 0 < H := by dsimp [H]; positivity
  let b := ComponentBounds.uniformLowerConstant S a M / (1 + T + H)
  have hbbase := ComponentBounds.uniformLowerConstant_pos (a := a) hS hM
  have hb : 0 < b := div_pos hbbase (by positivity)
  let c := min 1 (min (b / 2) (b / (4 * A)))
  have hc : 0 < c := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let C := max (2 * A * M ^ 2) (4 / H ^ 2)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro z g hE hP hz hg0 hclose hres
  by_cases hh : z.im ≤ H
  · have hzn : ‖z‖ ≤ T + H := by
      have ht := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz] at ht
      linarith [hJ z.re hE]
    have hlo : ∀ i, b ≤ ‖m z i‖ := by
      intro i
      calc
        b ≤ ComponentBounds.uniformLowerConstant S a M / (1 + ‖z‖) :=
          div_le_div_of_nonneg_left hbbase.le (by positivity) (by linarith)
        _ ≤ ‖m z i‖ := ComponentBounds.common_scaled_lower_bound hS
          (hupper z hE hz) (hsol z hE hz) hM (hmod z hE hz hh) i
    have hcloseb : ‖g - m z‖ ≤ b / 2 :=
      hclose.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsmall : 4 * A * ‖g - m z‖ ≤ b := by
      have hh' := hclose.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hmul := (le_div_iff₀ (by positivity : 0 < 4 * A)).mp hh'
      nlinarith
    have hbnd := bounded_height_stability S a z (m z) g b M A hb hM hA.le
      (BasicEstimates.component_ne_zero (hupper z hE hz)) (hsol z hE hz)
      hlo (hmod z hE hz hh) hcloseb hsmall (hlinear z hE hP hz hh)
    exact hbnd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have hheight : H ≤ z.im := (lt_of_not_ge hh).le
    have hbnd := large_height_stability S a z (m z) g s c ‖Model.residual S a z g‖
      hs hc.le (min_le_left _ _) (norm_nonneg _) hS hrow (hupper z hE hz)
      (hsol z hE hz) hg0
      (fun i => (norm_le_pi_norm (g - m z) i).trans hclose)
      (fun i => (norm_le_pi_norm (Model.residual S a z g) i).trans hres)
      (fun i => norm_le_pi_norm (Model.residual S a z g) i) hheight
    have hratio : 4 / z.im ^ 2 ≤ 4 / H ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hH)
        (pow_le_pow_left₀ hH.le hheight 2)
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro i
    exact (hbnd i).trans (mul_le_mul_of_nonneg_right
      (hratio.trans (le_max_right _ _)) (norm_nonneg _))

/-- A real boundary exception does not affect a region at fixed positive
complex distance from that point. -/
theorem stable_away_from_real_point [Nonempty ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (J : Set ℝ) (hJ : IsCompact J)
    (m : ℂ → ι → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (MainLinearBulk.closedStrip J))
    (hupper : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsDysonSolution S a z (m z))
    (a₀ : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hboundary : ∀ E ∈ J, E ≠ a₀ → Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : ι → ℂ),
      z.re ∈ J → δ ≤ ‖z - (a₀ : ℂ)‖ → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual S a z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual S a z g‖ := by
  let s : ℝ := ‖fun i => ∑ j, S i j‖
  have hs : 0 ≤ s := norm_nonneg _
  have hrow : ∀ i, ∑ j, S i j ≤ s := fun i =>
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H := 2 * (s + 1)
  let K₀ := MainLinearBulk.boundedStrip J H
  let K := K₀ ∩ {z : ℂ | δ ≤ ‖z - (a₀ : ℂ)‖}
  have hK₀ : IsCompact K₀ := MainLinearBulk.boundedStrip_compact J hJ H
  have hK : IsCompact K := hK₀.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hsub₀ : K₀ ⊆ MainLinearBulk.closedStrip J := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hsub : K ⊆ MainLinearBulk.closedStrip J := fun _ hz => hsub₀ hz.1
  have hbij : ∀ z ∈ K, Function.Bijective (InteriorStability.stabilityOperator S (m z)) := by
    intro z hz
    by_cases hi : 0 < z.im
    · exact InteriorStability.stability_bijective hS hi (hupper z (hsub hz)) (hsol z (hsub hz))
    · have him : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.1.2.1
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
      have hEn : z.re ≠ a₀ := by
        intro heq
        have hz0 : z - (a₀ : ℂ) = 0 := by rw [he, heq]; simp
        have hh : δ ≤ ‖z - (a₀ : ℂ)‖ := hz.2
        rw [hz0, norm_zero] at hh
        exact (not_le_of_gt hδ) hh
      simpa only [← he] using hboundary z.re hz.1.1 hEn
  obtain ⟨A, hA, hlinear⟩ := BulkCompact.uniform_dyson_bound K hK S m (hcont.mono hsub) hbij
  obtain ⟨M₀, hM₀⟩ := hK₀.exists_bound_of_continuousOn (hcont.mono hsub₀)
  obtain ⟨T₀, hT₀⟩ := hJ.exists_bound_of_continuousOn continuousOn_id
  apply stable_region_nonlinear_of_bounds S a J (fun z => δ ≤ ‖z - (a₀ : ℂ)‖) m
    (max 1 T₀) s A (max 1 M₀)
    (le_trans zero_le_one (le_max_left _ _)) hs hA
    (le_trans zero_le_one (le_max_left _ _)) hS hrow
  · intro E hE
    exact (hT₀ E hE).trans (le_max_right _ _)
  · intro z hE hz
    exact hupper z ⟨hE, hz.le⟩
  · intro z hE hz
    exact hsol z ⟨hE, hz.le⟩
  · intro z hE hz hh i
    exact (norm_le_pi_norm _ i).trans ((hM₀ z ⟨hE, hz.le, hh⟩).trans (le_max_right _ _))
  · intro z hE haway hz hh u
    exact hlinear z ⟨⟨hE, hz.le, hh⟩, haway⟩ u

namespace NB

/-- M7(i) in the exceptional model away from its spectral point.  The
exclusion is |z-a₀|≥δ, so purely vertical points are included. -/
theorem main_theorem_seven_away
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V) [Fintype G.Edge] (root : G.Edge)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (hbase : Resonance.StronglyConnected G.Adj)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := G.Edge))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (a₀ : ℝ) (m : ℂ → G.Edge → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution G.matrix (fun _ => a₀) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ J → δ ≤ ‖z - (a₀ : ℂ)‖ → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual G.matrix (fun _ => a₀) z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual G.matrix (fun _ => a₀) z g‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  obtain ⟨hcont, hu, he⟩ := Exceptional.canonical_closed_strip_data algebraic puiseux G.matrix
    (fun _ => a₀) G.matrix_nonnegative m hupper heq J hregular hbulk
  have hbij : ∀ E ∈ J, E ≠ a₀ → Function.Bijective
      (InteriorStability.stabilityOperator G.matrix (Boundary.boundaryVector m (E : ℂ))) := by
    intro E hE hEn
    apply BulkBoundary.NB.boundary_bijective G (fun _ => a₀) E (Boundary.boundaryVector m (E : ℂ))
      hd root hbase (hbulk E hE)
      (Boundary.family_boundary_equation algebraic puiseux G.matrix (fun _ => a₀)
        G.matrix_nonnegative m hupper heq E (hregular E hE)).2.2
    rintro ⟨ha, _⟩
    exact hEn (ha (G.head root)).symm
  obtain ⟨c,C,hc,hC,hb⟩ := stable_away_from_real_point G.matrix (fun _ => a₀) J hJ
    (Boundary.boundaryVector m) G.matrix_nonnegative hcont hu he a₀ δ hδ hbij
  refine ⟨c,C,hc,hC,?_⟩
  intro z g hzJ haway hz hg0 hclose hres
  have hh := hb z g hzJ haway hz hg0
  rw [Boundary.family_extension_agrees G.matrix (fun _ => a₀) G.matrix_nonnegative
    m hupper heq z hz] at hh
  exact hh hclose hres

end NB
end NonSymmetricDyson.Full.Nonlinear
