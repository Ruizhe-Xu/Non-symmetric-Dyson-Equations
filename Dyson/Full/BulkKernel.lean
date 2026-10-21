import Dyson.Full.BulkMarkov

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkKernel
open Resonance
variable {V : Type*} [Fintype V]

theorem exists_positive_support_bound (Q : Matrix V V ℝ) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa ≤ 1 ∧
      ∀ i j, 0 < Q i j → kappa ≤ Q i j := by
  let f : V × V → ℝ := fun p => if 0 < Q p.1 p.2 then min 1 (Q p.1 p.2) else 1
  have hf0 (p : V × V) : 0 < f p := by
    dsimp [f]
    split <;> positivity
  have hf1 (p : V × V) : f p ≤ 1 := by
    dsimp [f]
    split
    · exact min_le_left _ _
    · exact le_rfl
  refine ⟨∏ p, f p, Finset.prod_pos (fun p _ => hf0 p),
    Finset.prod_le_one (fun p _ => le_of_lt (hf0 p)) (fun p _ => hf1 p), ?_⟩
  intro i j hij
  have hp : (∏ p ∈ Finset.univ.erase (i,j), f p) ≤ 1 :=
    Finset.prod_le_one (fun p _ => le_of_lt (hf0 p)) (fun p _ => hf1 p)
  have heq : (∏ p, f p) = f (i,j) * (∏ p ∈ Finset.univ.erase (i,j), f p) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ (i,j))).symm
  have hh : (∏ p, f p) ≤ f (i,j) := by
    rw [heq]
    exact mul_le_of_le_one_right (le_of_lt (hf0 (i,j))) hp
  exact hh.trans (by dsimp [f]; rw [if_pos hij]; exact min_le_right _ _)

theorem weight_inverse {H : Type*} [CommGroup H] (E : V → V → Prop)
    (phase : V → H) {a b : V} (p : Walk E a b) :
    p.weight (fun i => (phase i)⁻¹) = (p.weight phase)⁻¹ := by
  induction p with
  | nil => simp
  | cons h p ih => simp [Walk.weight_cons, ih, mul_comm]

theorem cycleResonant_inverse_iff {H : Type*} [CommGroup H]
    (E : V → V → Prop) (phase : V → H) :
    CycleResonant E (fun i => (phase i)⁻¹) ↔ CycleResonant E phase := by
  constructor
  · intro hc a p
    have hh := hc a p
    rw [weight_inverse] at hh
    simpa using congrArg Inv.inv hh
  · intro hc a p
    rw [weight_inverse, hc a p, inv_one]

/-- Any nonzero kernel vector of a stochastic phase matrix forces the exact
cycle resonance. No torus metric assumption is needed for this implication. -/
theorem resonance_of_kernel [Nonempty V]
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hc : StronglyConnected (fun i j => 0 < Q i j))
    (u : V → Circle) (w : V → ℂ) (hw : w ≠ 0)
    (hker : MarkovStability.phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 w = 0) :
    CycleResonant (fun i j => 0 < Q i j) u := by
  obtain ⟨kappa, hk0, hk1, hsupport⟩ := exists_positive_support_bound Q
  have hh := BulkMarkov.defect_lower_bound (fun i j => 0 < Q i j) hc Q hQ hrow
    kappa hk0 hk1 hsupport u 1 (by norm_num) (by norm_num) w
  rw [hker, norm_zero, mul_zero] at hh
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hp : 0 < kappa ^ Fintype.card V := pow_pos hk0 _
  have hs : (PhaseDefect.delta (fun i j => 0 < Q i j) u) ^ 2 = 0 := by
    have hh' : (kappa ^ Fintype.card V * ‖w‖) *
        (PhaseDefect.delta (fun i j => 0 < Q i j) u) ^ 2 ≤ 0 := by nlinarith
    have hsle : (PhaseDefect.delta (fun i j => 0 < Q i j) u) ^ 2 ≤ 0 := by
      by_contra hnot
      have hpos := mul_pos (mul_pos hp hn) (lt_of_not_ge hnot)
      exact (not_le_of_gt hpos) hh'
    exact le_antisymm hsle (sq_nonneg _)
  have hd : PhaseDefect.delta (fun i j => 0 < Q i j) u = 0 := by nlinarith
  exact (PhaseDefect.delta_eq_zero_iff_cycleResonant _ u (Classical.arbitrary V) hc).mp hd

end NonSymmetricDyson.Full.BulkKernel
