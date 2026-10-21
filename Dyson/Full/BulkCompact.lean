import Dyson.InteriorStability
import Dyson.Full.BulkBoundary
import Mathlib

noncomputable section
open scoped Topology BigOperators

namespace NonSymmetricDyson.Full.BulkCompact
variable {V Z : Type*} [Fintype V] [Nonempty V] [TopologicalSpace Z]

/-- Finite-dimensional compactness turns pointwise kernel triviality into an
actual uniform inverse estimate. This general lemma is proved, not assumed. -/
theorem uniform_lower_bound
    (K : Set Z) (hK : IsCompact K)
    (L : Z → (V → ℂ) →L[ℂ] (V → ℂ)) (hL : ContinuousOn L K)
    (hker : ∀ z ∈ K, ∀ v, L z v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ v : V → ℂ, ‖v‖ ≤ C * ‖L z v‖ := by
  by_cases hne : K.Nonempty
  · let U := {v : V → ℂ // ‖v‖ = 1}
    have hU : IsCompact {v : V → ℂ | ‖v‖ = 1} := by
      simpa [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : V → ℂ) 1
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : CompactSpace U := isCompact_iff_compactSpace.mp hU
    letI : Nonempty K := hne.to_subtype
    letI : Nonempty U := ⟨⟨fun _ => 1, by simp⟩⟩
    let f : K × U → ℝ := fun p => ‖L p.1.val p.2.val‖
    have hf : Continuous f := by
      have hLc : Continuous (fun z : K => L z.val) := hL.restrict
      exact ((hLc.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp continuous_snd)).norm
    obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set (K × U)).Nonempty) hf.continuousOn
    have hpos : 0 < f p := by
      apply norm_pos_iff.mpr
      intro he
      have hz := hker p.1.val p.1.property p.2.val he
      have hn := p.2.property
      rw [hz, norm_zero] at hn
      norm_num at hn
    refine ⟨(f p)⁻¹, inv_pos.mpr hpos, ?_⟩
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let c : ℂ := (‖v‖ : ℂ)⁻¹
    have hcn : ‖c‖ = ‖v‖⁻¹ := by simp [c, Complex.norm_real]
    have hvn : ‖c • v‖ = 1 := by rw [norm_smul, hcn, inv_mul_cancel₀ (ne_of_gt hn)]
    have hh := hp (Set.mem_univ ((⟨z, hz⟩, ⟨c • v, hvn⟩) : K × U))
    change f p ≤ ‖L z (c • v)‖ at hh
    rw [map_smul, norm_smul, hcn] at hh
    have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hn)
    have hcancel : (‖v‖⁻¹ * ‖L z v‖) * ‖v‖ = ‖L z v‖ := by field_simp [ne_of_gt hn]
    rw [hcancel] at hmul
    have hd : ‖v‖ ≤ ‖L z v‖ / f p := (le_div_iff₀ hpos).mpr (by nlinarith)
    simpa [div_eq_mul_inv, mul_comm] using hd
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact False.elim (hne ⟨z, hz⟩)

def stabilityCLM (S : Matrix V V ℝ) (m : V → ℂ) :
    (V → ℂ) →L[ℂ] (V → ℂ) :=
  (InteriorStability.stabilityOperator S m).toContinuousLinearMap

theorem stabilityCLM_continuousOn (K : Set Z) (S : Matrix V V ℝ)
    (m : Z → V → ℂ) (hm : ContinuousOn m K) :
    ContinuousOn (fun z => stabilityCLM S (m z)) K := by
  apply continuousOn_clm_apply.mpr
  intro x
  apply continuousOn_pi.mpr
  intro i
  change ContinuousOn (fun z => x i - (m z i) ^ 2 * ∑ j, (S i j : ℂ) * x j) K
  exact continuousOn_const.sub
    (((continuous_apply i).comp_continuousOn hm).pow 2 |>.mul continuousOn_const)

theorem uniform_dyson_bound (K : Set Z) (hK : IsCompact K) (S : Matrix V V ℝ)
    (m : Z → V → ℂ) (hm : ContinuousOn m K)
    (hbij : ∀ z ∈ K, Function.Bijective (InteriorStability.stabilityOperator S (m z))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ x : V → ℂ,
      ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator S (m z) x‖ := by
  apply uniform_lower_bound K hK (fun z => stabilityCLM S (m z))
    (stabilityCLM_continuousOn K S m hm)
  intro z hz x hx
  apply (hbij z hz).injective
  simpa [stabilityCLM] using hx

/-- Uniform regular bulk stability on an arbitrary compact part of the
closed upper half-plane, derived from the actual Dyson solution and the
precise symmetric exception. -/
theorem symmetric_uniform_bound (K : Set ℂ) (hK : IsCompact K)
    (S : Matrix V V ℝ) (a : V → ℝ) (m : ℂ → V → ℂ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => S i j ≠ 0))
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hcont : ContinuousOn m K)
    (hupper : ∀ z ∈ K, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ K, BasicEstimates.IsDysonSolution S a z (m z))
    (hheight : ∀ z ∈ K, 0 ≤ z.im)
    (hexception : ∀ z ∈ K, z.im = 0 → ¬ ((∀ i, a i = z.re) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ x : V → ℂ,
      ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator S (m z) x‖ := by
  apply uniform_dyson_bound K hK S m hcont
  intro z hz
  by_cases hi : 0 < z.im
  · exact InteriorStability.stability_bijective hS hi (hupper z hz) (hsol z hz)
  · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hi) (hheight z hz)
    have he : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hi0
    apply BulkBoundary.symmetric_boundary_bijective S a z.re (m z) hS hc hsymm
      (hupper z hz) _ (hexception z hz hi0)
    simpa only [← he] using hsol z hz

namespace NB
open Nonbacktracking
variable (G : BaseGraph V) [Fintype G.Edge]

theorem uniform_bound (K : Set ℂ) (hK : IsCompact K)
    (a : V → ℝ) (m : ℂ → G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : Resonance.StronglyConnected G.Adj)
    (hcont : ContinuousOn m K)
    (hupper : ∀ z ∈ K, BasicEstimates.IsUpperSolution (m z))
    (hsol : ∀ z ∈ K, BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z (m z))
    (hheight : ∀ z ∈ K, 0 ≤ z.im)
    (hexception : ∀ z ∈ K, z.im = 0 → ¬ ((∀ y, a y = z.re) ∧
      ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ x : G.Edge → ℂ,
      ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator G.matrix (m z) x‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  apply uniform_dyson_bound K hK G.matrix m hcont
  intro z hz
  by_cases hi : 0 < z.im
  · exact InteriorStability.stability_bijective G.matrix_nonnegative hi (hupper z hz) (hsol z hz)
  · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hi) (hheight z hz)
    have he : z = (z.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hi0
    apply BulkBoundary.NB.boundary_bijective G a z.re (m z) hd root hbase
      (hupper z hz) _ (hexception z hz hi0)
    simpa only [← he] using hsol z hz

end NB
end NonSymmetricDyson.Full.BulkCompact
