import Dyson.Paper.BoundaryProofs
import Dyson.Full.AtomRemoval

/-! Compact uniform convergence of the actual pole-subtracted transform,
as used in the original proof before Stieltjes inversion. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set MeasureTheory
namespace NonSymmetricDyson.Paper.BoundaryPoleUniform
open Full Full.Boundary Full.ExternalAlgebraic
variable {ι : Type*} [Fintype ι]

theorem atomRemoved_extension_continuous
    (m : ℂ → ι → ℂ) (i : ι) (μ : Measure ℝ) (A : Finset ℝ)
    (hcont : ContinuousOn (boundaryVector m) (commonRegularDomain m))
    (hA : (A : Set ℝ) ⊆ singularUnion m) :
    ContinuousOn (atomRemoved μ (fun z => boundaryVector m z i) A) (commonRegularDomain m) := by
  apply ((continuous_apply i).comp_continuousOn hcont).sub
  apply continuousOn_finset_sum A
  intro τ hτ
  apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
  intro z hz
  intro he
  have hzτ : z = (τ:ℂ) := (sub_eq_zero.mp he).symm
  subst z
  rcases hz with hi | ⟨x,hx,he⟩
  · simpa [upper] using hi
  · have hxτ : x=τ := Complex.ofReal_injective he
    subst x
    exact hx (hA hτ)

/-- The convergence is uniform on every compact set disjoint from all
singularities, for the genuine finite atomic subtraction. -/
theorem atomRemoved_compact_vertical_uniform
    (m : ℂ → ι → ℂ) (i : ι) (μ : Measure ℝ) (A : Finset ℝ)
    (hcont : ContinuousOn (boundaryVector m) (commonRegularDomain m))
    (hagree : ∀ z : ℂ, 0 < z.im → boundaryVector m z = m z)
    (hA : (A : Set ℝ) ⊆ singularUnion m)
    (K : Set ℝ) (hK : IsCompact K) (hKreg : K ⊆ (singularUnion m)ᶜ) :
    TendstoUniformlyOn
      (fun η x => atomRemoved μ (fun z => m z i) A (Full.Boundary.vertical x η))
      (fun x => atomRemoved μ (fun z => boundaryVector m z i) A (x:ℂ))
      (𝓝[>] (0:ℝ)) K := by
  let F : ℝ → ℝ → ℂ := fun η x =>
    atomRemoved μ (fun z => boundaryVector m z i) A (Full.Boundary.vertical x η)
  have hc : ContinuousOn (Function.uncurry F) (Icc (0:ℝ) 1 ×ˢ K) := by
    apply (atomRemoved_extension_continuous m i μ A hcont hA).comp
      (show ContinuousOn (fun p : ℝ × ℝ => Full.Boundary.vertical p.2 p.1)
        (Icc (0:ℝ) 1 ×ˢ K) from (by unfold Full.Boundary.vertical; fun_prop))
    intro p hp
    by_cases hi : 0 < p.1
    · exact Or.inl (by simpa using hi)
    · have hz : p.1=0 := le_antisymm (le_of_not_gt hi) hp.1.1
      exact Or.inr ⟨p.2,hKreg hp.2,by simp [Full.Boundary.vertical,hz]⟩
  have hu := ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn
    (F := F) (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hfilter : (𝓝[>] (0:ℝ)) ≤ 𝓝[Icc (0:ℝ) 1] (0:ℝ) := by
    rw [nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0:ℝ)<1)]
    exact nhdsWithin_mono _ Ioi_subset_Ici_self
  have hu' := (hu.tendstoUniformlyOnFilter.mono_left hfilter).tendstoUniformlyOn
  have he : F 0 = fun (x : ℝ) => atomRemoved μ (fun z => boundaryVector m z i) A (x:ℂ) := by
    funext x
    simp [F,Full.Boundary.vertical]
  rw [he] at hu'
  apply hu'.congr
  filter_upwards [self_mem_nhdsWithin] with η hη
  intro x _
  simp only [F,atomRemoved]
  rw [hagree (Full.Boundary.vertical x η) (by simpa using hη)]

end NonSymmetricDyson.Paper.BoundaryPoleUniform
