import Dyson.Full.BulkTorus
import Dyson.Full.BulkKernel
import Dyson.Full.BulkGraph

noncomputable section
open scoped Classical
namespace NonSymmetricDyson.Full.BulkDistance
open Resonance
variable {V : Type*} [Fintype V] (E : V → V → Prop)

theorem weight_continuous {a b : V} (p : Walk E a b) :
    Continuous (fun u : V → Circle => p.weight u) := by
  induction p with
  | nil => exact continuous_const
  | @cons a b c hab rest ih => exact (continuous_apply a).mul ih

theorem resonance_closed : IsClosed {u : V → Circle | CycleResonant E u} := by
  simp only [CycleResonant, Set.setOf_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun p =>
    isClosed_eq (weight_continuous E p) continuous_const

theorem resonance_nonempty : Set.Nonempty {u : V → Circle | CycleResonant E u} := by
  refine ⟨1, cycleResonant_of_hasVertexGauge _ ⟨1, ?_⟩⟩
  intro a b hab
  simp

theorem exists_nearest (u : V → Circle) :
    ∃ v : V → Circle, CycleResonant E v ∧
      ‖BulkTorus.difference u v‖ = BulkTorus.resonanceDistance E u := by
  have hf : Continuous (fun v => ‖BulkTorus.difference u v‖) := by
    apply Continuous.norm
    apply continuous_pi
    intro i
    change Continuous (fun v : V → Circle => (u i : ℂ) - (v i : ℂ))
    fun_prop
  obtain ⟨v, hv, hmin⟩ := (resonance_closed E).isCompact.exists_isMinOn
    (resonance_nonempty E) hf.continuousOn
  refine ⟨v, hv, le_antisymm ?_ (BulkTorus.resonanceDistance_le E u v hv)⟩
  apply le_csInf
  · exact ⟨‖BulkTorus.difference u v‖, v, hv, rfl⟩
  · rintro r ⟨w, hw, rfl⟩
    exact hmin hw

theorem inverse_difference (u v : V → Circle) :
    ‖BulkTorus.difference (fun i => (u i)⁻¹) (fun i => (v i)⁻¹)‖ =
      ‖BulkTorus.difference u v‖ := by
  have hi (i : V) : ‖BulkTorus.difference (fun i => (u i)⁻¹) (fun i => (v i)⁻¹) i‖ =
      ‖BulkTorus.difference u v i‖ := by
    simp only [BulkTorus.difference, Circle.coe_inv_eq_conj, ← map_sub, Complex.norm_conj]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [hi]
    exact norm_le_pi_norm _ i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← hi]
    exact norm_le_pi_norm _ i

theorem inverse_distance (u : V → Circle) :
    BulkTorus.resonanceDistance E (fun i => (u i)⁻¹) = BulkTorus.resonanceDistance E u := by
  have hle (v : V → Circle) : BulkTorus.resonanceDistance E (fun i => (v i)⁻¹) ≤
      BulkTorus.resonanceDistance E v := by
    obtain ⟨w, hw, he⟩ := exists_nearest E v
    have hi := BulkTorus.resonanceDistance_le E (fun i => (v i)⁻¹)
      (fun i => (w i)⁻¹) ((BulkKernel.cycleResonant_inverse_iff E w).mpr hw)
    rwa [inverse_difference, he] at hi
  exact le_antisymm (hle u) (by simpa only [inv_inv] using hle (fun i => (u i)⁻¹))

theorem defect_le_distance (root : V) (hc : StronglyConnected E) (u : V → Circle) :
    PhaseDefect.delta E u ≤ BulkTorus.resonanceDistance E u := by
  obtain ⟨v, hv, he⟩ := exists_nearest E u
  obtain ⟨gamma, hg⟩ := hasVertexGauge_of_cycleResonant v root hc hv
  have hb : PhaseDefect.edgeDefect E u gamma ≤ ‖BulkTorus.difference u v‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro e
    change ‖(u e.val.1 : ℂ) - ((gamma e.val.1)⁻¹ * gamma e.val.2 : Circle)‖ ≤ _
    rw [← hg _ _ e.property]
    exact norm_le_pi_norm (BulkTorus.difference u v) e.val.1
  exact (BulkPhase.delta_le_edgeDefect E u gamma).trans (hb.trans_eq he)

theorem nonbipartite_distance (hs : ∀ i j, E i j → E j i)
    (hc : StronglyConnected E)
    (hn : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := E) part)
    (u : V → Circle) :
    BulkTorus.resonanceDistance E u = ‖BulkTorus.difference u 1‖ := by
  obtain ⟨v, hv, he⟩ := exists_nearest E u
  have hv1 : v = 1 := by
    funext i
    by_contra h
    exact hn (BulkGraph.bipartition_of_nontrivial_resonance hs hc v hv i h)
  simpa [hv1] using he.symm

end NonSymmetricDyson.Full.BulkDistance
