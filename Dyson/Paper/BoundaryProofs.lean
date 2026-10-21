import Dyson.Paper.Foundations
import Dyson.Full.MainBoundary
import Dyson.Full.BoundaryBounds

/-! Explicit proof steps in the revised boundary chapter: uniqueness of the
continuous extension and uniform Full.Boundary.vertical convergence on compact regular sets. -/
noncomputable section
open scoped Topology
open Filter Set
namespace NonSymmetricDyson.Paper.BoundaryProofs
open Full Full.Boundary Full.ExternalAlgebraic Full.Foundations
variable {ι : Type*} [Fintype ι]

/-- Continuous extension determines every boundary value uniquely. -/
theorem continuous_extension_unique
    (m F : ℂ → ι → ℂ) (I : Set ℝ)
    (hF : ContinuousOn F (closedStrip I))
    (hagree : ∀ z : ℂ, z.re ∈ I → 0 < z.im → F z = m z)
    (hlim : ∀ E ∈ I, Tendsto (fun η => m (Full.Boundary.vertical E η))
      (𝓝[>] (0 : ℝ)) (𝓝 (boundaryVector m (E:ℂ))))
    (hinterior : ∀ z : ℂ, 0 < z.im → boundaryVector m z = m z) :
    EqOn F (boundaryVector m) (closedStrip I) := by
  intro z hz
  by_cases hi : 0 < z.im
  · rw [hinterior z hi]
    exact hagree z hz.1 hi
  · have hz0 : z.im = 0 := le_antisymm (le_of_not_gt hi) hz.2
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz0]
    have hv : Tendsto (fun η : ℝ => Full.Boundary.vertical z.re η) (𝓝[>] (0 : ℝ))
        (𝓝[closedStrip I] z) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [he] using vertical_tendsto z.re
      · filter_upwards [self_mem_nhdsWithin] with η hη
        exact ⟨by simpa [Full.Boundary.vertical] using hz.1, by simpa using hη.le⟩
    have ht := (hF z hz).tendsto.comp hv
    have ht' : Tendsto (fun η : ℝ => m (Full.Boundary.vertical z.re η)) (𝓝[>] (0 : ℝ)) (𝓝 (F z)) := by
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact hagree _ (by simpa [Full.Boundary.vertical] using hz.1) (by simpa using hη)
    exact tendsto_nhds_unique ht' (by simpa only [he] using hlim z.re hz.1)

/-- Compactness upgrades the continuous boundary extension to the uniform
Full.Boundary.vertical convergence used before Stieltjes inversion in the source proof. -/
theorem compact_vertical_uniform
    (m : ℂ → ι → ℂ) (K : Set ℝ) (hK : IsCompact K)
    (hcont : ContinuousOn (boundaryVector m) (commonRegularDomain m))
    (hKreg : K ⊆ (singularUnion m)ᶜ)
    (hagrees : ∀ z : ℂ, 0 < z.im → boundaryVector m z = m z) :
    TendstoUniformlyOn (fun η x => m (Full.Boundary.vertical x η))
      (fun x => boundaryVector m (x:ℂ)) (𝓝[>] (0 : ℝ)) K := by
  let F : ℝ → ℝ → (ι → ℂ) := fun η x => boundaryVector m (Full.Boundary.vertical x η)
  have hc : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) 1 ×ˢ K) := by
    apply hcont.comp (show ContinuousOn (fun p : ℝ × ℝ => Full.Boundary.vertical p.2 p.1)
      (Icc (0:ℝ) 1 ×ˢ K) from (by unfold Full.Boundary.vertical; fun_prop))
    intro p hp
    by_cases hi : 0 < p.1
    · exact Or.inl (by simpa using hi)
    · have hz : p.1 = 0 := le_antisymm (le_of_not_gt hi) hp.1.1
      exact Or.inr ⟨p.2, hKreg hp.2, by simp [Full.Boundary.vertical,hz]⟩
  have hu := ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn (F := F)
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hfilter : (𝓝[>] (0:ℝ)) ≤ 𝓝[Icc (0:ℝ) 1] (0:ℝ) := by
    rw [nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0:ℝ)<1)]
    exact nhdsWithin_mono _ Ioi_subset_Ici_self
  have hu' := (hu.tendstoUniformlyOnFilter.mono_left hfilter).tendstoUniformlyOn
  have he : F 0 = (fun (x : ℝ) => boundaryVector m (x:ℂ)) := by
    funext x
    simp [F,Full.Boundary.vertical]
  rw [he] at hu'
  apply hu'.congr
  filter_upwards [self_mem_nhdsWithin] with η hη
  intro x _
  exact hagrees _ (by simpa using hη)

/-- Actual M2 application of the compact-uniform convergence step. -/
theorem dyson_compact_vertical_uniform
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (K : Set ℝ) (hK : IsCompact K) (hKreg : K ⊆ (singularUnion m)ᶜ) :
    TendstoUniformlyOn (fun η x => m (Full.Boundary.vertical x η))
      (fun x => boundaryVector m (x:ℂ)) (𝓝[>] (0 : ℝ)) K :=
  compact_vertical_uniform m K hK
    (family_boundary_continuous algebraic puiseux S a hS m hupper heq) hKreg
    (family_extension_agrees S a hS m hupper heq)

/-- The boundedness clause of M2 gives a continuous extension on the entire
closed upper half-plane, and that extension is unique on its stated domain. -/
theorem bounded_unique_continuous_extension
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (M : ℝ) (hbound : ∀ z ∈ upper, ∀ i, ‖m z i‖ ≤ M) :
    ContinuousOn (boundaryVector m) closedUpper ∧
      (∀ z ∈ upper, boundaryVector m z = m z) ∧
      ∀ F : ℂ → ι → ℂ, ContinuousOn F closedUpper →
        (∀ z ∈ upper, F z = m z) → EqOn F (boundaryVector m) closedUpper := by
  have hb : ∀ z : ℂ, z.re ∈ (univ : Set ℝ) → 0 < z.im → ∀ i, ‖m z i‖ ≤ M :=
    fun z _ hz => hbound z hz
  have hdom : closedStrip (univ : Set ℝ) = closedUpper := by ext z; simp [closedStrip,closedUpper]
  have hc := family_closedStrip_continuous algebraic puiseux S a hS m hupper heq univ M hb
  have ha := family_extension_agrees S a hS m hupper heq
  refine ⟨hdom ▸ hc, ha, ?_⟩
  intro F hF hagree
  rw [← hdom] at hF ⊢
  apply continuous_extension_unique m F univ hF (fun z _ hz => hagree z hz) ?_ ha
  intro E _
  exact family_boundary_limits algebraic puiseux S a hS m hupper heq E
    (strip_disjoint_singular m univ M hb E (mem_univ E))

end NonSymmetricDyson.Paper.BoundaryProofs
