import Dyson.Full.Nonlinear
import Dyson.Full.MainLinearBulk
import Dyson.Full.OffSupport

/-! Uniform stable-region nonlinear estimates, including all positive heights. -/

noncomputable section
open scoped BigOperators Topology

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

/-- Assembly of bounded-height absorption and the corrected large-height
argument. The intermediate hypotheses concern actual linear operators and
actual solution moduli; the applications below construct them. -/
theorem stable_strip_nonlinear_of_bounds
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (J : Set ℝ) (m : ℂ → ι → ℂ)
    (T s A M : ℝ) (hT : 0 ≤ T) (hs : 0 ≤ s) (hA : 0 < A) (hM : 0 ≤ M)
    (hS : ∀ i j, 0 ≤ S i j) (hrow : ∀ i, ∑ j, S i j ≤ s)
    (hJ : ∀ E ∈ J, |E| ≤ T)
    (hupper : ∀ z : ℂ, z.re ∈ J → 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z : ℂ, z.re ∈ J → 0 < z.im → BasicEstimates.IsDysonSolution S a z (m z))
    (hmod : ∀ z : ℂ, z.re ∈ J → 0 < z.im → z.im ≤ 2 * (s + 1) → ∀ i, ‖m z i‖ ≤ M)
    (hlinear : ∀ z : ℂ, z.re ∈ J → 0 < z.im → z.im ≤ 2 * (s + 1) →
      ∀ u, ‖u‖ ≤ A * ‖InteriorStability.stabilityOperator S (m z) u‖) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : ι → ℂ),
      z.re ∈ J → 0 < z.im → (∀ i, g i ≠ 0) →
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
  intro z g hE hz hg0 hclose hres
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
      hlo (hmod z hE hz hh) hcloseb hsmall (hlinear z hE hz hh)
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

/-- Stable bulk strips with a compact base and continuous physical boundary
values. Boundary invertibility is an intermediate input and is discharged by
the graph-specific corollary below. -/
theorem stable_strip_nonlinear_of_boundary_bijective [Nonempty ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (J : Set ℝ) (hJ : IsCompact J)
    (m : ℂ → ι → ℂ) (hS : ∀ i j, 0 ≤ S i j)
    (hcont : ContinuousOn m (MainLinearBulk.closedStrip J))
    (hupper : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsDysonSolution S a z (m z))
    (hboundary : ∀ E ∈ J, Function.Bijective (InteriorStability.stabilityOperator S (m (E : ℂ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : ι → ℂ),
      z.re ∈ J → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual S a z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual S a z g‖ := by
  let s : ℝ := ‖fun i => ∑ j, S i j‖
  have hs : 0 ≤ s := norm_nonneg _
  have hrow : ∀ i, ∑ j, S i j ≤ s := fun i =>
    (le_abs_self _).trans (norm_le_pi_norm (fun i => ∑ j, S i j) i)
  let H := 2 * (s + 1)
  let K := MainLinearBulk.boundedStrip J H
  have hK : IsCompact K := MainLinearBulk.boundedStrip_compact J hJ H
  have hsub : K ⊆ MainLinearBulk.closedStrip J := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hbij : ∀ z ∈ K, Function.Bijective (InteriorStability.stabilityOperator S (m z)) := by
    intro z hz
    by_cases hi : 0 < z.im
    · exact InteriorStability.stability_bijective hS hi (hupper z (hsub hz)) (hsol z (hsub hz))
    · have him : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2.1
      have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
      simpa only [← he] using hboundary z.re hz.1
  obtain ⟨A, hA, hlinear⟩ := BulkCompact.uniform_dyson_bound K hK S m (hcont.mono hsub) hbij
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  obtain ⟨T₀, hT₀⟩ := hJ.exists_bound_of_continuousOn continuousOn_id
  apply stable_strip_nonlinear_of_bounds S a J m (max 1 T₀) s A (max 1 M₀)
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
  · intro z hE hz hh u
    exact hlinear z ⟨hE, hz.le, hh⟩ u

namespace NB

open Nonbacktracking

variable {V : Type*} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

/-- M7(i), stable bulk: the exact graph exception is excluded and the constants
are uniform over the entire upper strip. -/
theorem stable_bulk_nonlinear
    (a : V → ℝ) (J : Set ℝ) (hJ : IsCompact J) (m : ℂ → G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : Resonance.StronglyConnected G.Adj)
    (hcont : ContinuousOn m (MainLinearBulk.closedStrip J))
    (hupper : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ MainLinearBulk.closedStrip J,
      BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (hexception : ∀ E ∈ J, ¬ ((∀ y, a y = E) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : G.Edge → ℂ),
      z.re ∈ J → 0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - m z‖ ≤ c → ‖Model.residual G.matrix (G.terminalShift a) z g‖ ≤ c →
      ‖g - m z‖ ≤ C * ‖Model.residual G.matrix (G.terminalShift a) z g‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  apply stable_strip_nonlinear_of_boundary_bijective G.matrix (G.terminalShift a) J hJ m
    G.matrix_nonnegative hcont hupper hsol
  intro E hE
  apply BulkBoundary.NB.boundary_bijective G a E (m (E : ℂ)) hd root hbase
    (hupper (E : ℂ) (by simpa [MainLinearBulk.closedStrip] using hE))
    (hsol (E : ℂ) (by simpa [MainLinearBulk.closedStrip] using hE)) (hexception E hE)

end NB

/-- M7(i), off the support: actual Stieltjes bounds and the proved exterior
linear estimate are used over a fixed bounded energy region and all heights. -/
theorem off_support_nonlinear
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (μ : ι → MeasureTheory.Measure ℝ)
    (hμ : ∀ i, MeasureTheory.IsProbabilityMeasure (μ i)) (hS : ∀ i j, 0 ≤ S i j)
    (T A R Sigma ε : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hSigma : 0 ≤ Sigma) (hε : 0 < ε)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hsupport : ∀ i, ∀ᵐ t ∂μ i, |t| ≤ Sigma)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution
      (fun i => Poisson.stieltjes (μ i) z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z
      (fun i => Poisson.stieltjes (μ i) z)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (g : ι → ℂ),
      |z.re| ≤ T → (∀ i, ∀ᵐ t ∂μ i, ε ≤ |t - z.re|) →
      0 < z.im → (∀ i, g i ≠ 0) →
      ‖g - (fun i => Poisson.stieltjes (μ i) z)‖ ≤ c →
      ‖Model.residual S a z g‖ ≤ c →
      ‖g - (fun i => Poisson.stieltjes (μ i) z)‖ ≤ C * ‖Model.residual S a z g‖ := by
  letI : ∀ i, MeasureTheory.IsProbabilityMeasure (μ i) := hμ
  let J : Set ℝ := {E | |E| ≤ T ∧ ∀ i, ∀ᵐ t ∂μ i, ε ≤ |t - E|}
  let m : ℂ → ι → ℂ := fun z i => Poisson.stieltjes (μ i) z
  obtain ⟨L, hL, hlinear⟩ := OffSupport.exterior_uniform_bound S a μ hμ hS A R Sigma ε
    hA hR hSigma hε ha hrow hsupport hupper hsol
  have hpoint : ∀ z : ℂ, Poisson.point z.re z.im = z := by
    intro z
    apply Complex.ext <;> simp [Poisson.point]
  obtain ⟨c, C, hc, hC, hbound⟩ := stable_strip_nonlinear_of_bounds S a J m T R L ε⁻¹
    hT hR hL (inv_nonneg.mpr hε.le) hS hrow (fun E hE => hE.1)
    (fun z _ hz => hupper z hz) (fun z _ hz => hsol z hz)
    (by
      intro z hE hz hh i
      have hn := Poisson.stieltjes_norm_of_gap (μ i) hε (hE.2 i) (η := z.im)
      simpa only [hpoint z] using hn)
    (by
      intro z hE hz hh u
      simpa only [hpoint z] using hlinear z.re z.im hz.le hE.2 u)
  refine ⟨c, C, hc, hC, ?_⟩
  intro z g hreal hgap hz hg0 hclose hres
  exact hbound z g ⟨hreal, hgap⟩ hz hg0 hclose hres

end NonSymmetricDyson.Full.Nonlinear
