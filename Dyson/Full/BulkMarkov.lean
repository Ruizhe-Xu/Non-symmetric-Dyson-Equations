import Dyson.Full.BulkPhase
import Dyson.Full.BulkTorus

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkMarkov
universe u
open Resonance MarkovStability
variable {V : Type u} [Fintype V]

theorem residual_at_one (Q : Matrix V V ℝ) (u : V → Circle)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (w : V → ℂ) :
    ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 w‖ ≤
      2 * ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
  have hgap := phase_markov_lower_bound Q (fun i => (u i : ℂ)) lam
    hQ hrow (fun i => Circle.norm_coe (u i)) hl0 w
  have hcontr := markov_norm_contraction Q hQ hrow w
  have hid : phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 w =
      phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w -
        ((1 - lam : ℝ) : ℂ) • Model.action Q w := by
    ext i
    simp only [phaseMarkovOperator_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_one, Complex.ofReal_sub, Model.action_apply]
    ring
  rw [hid]
  calc
    _ ≤ ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ +
        ‖((1 - lam : ℝ) : ℂ) • Model.action Q w‖ := norm_sub_le _ _
    _ = ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ +
        (1 - lam) * ‖Model.action Q w‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hl1)]
    _ ≤ ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ +
        (1 - lam) * ‖w‖ := by
      exact add_le_add_left (mul_le_mul_of_nonneg_left hcontr (sub_nonneg.mpr hl1)) _
    _ ≤ _ := by linarith

/-- Homogeneous form of the phase estimate; this contains the phase term,
including the boundary parameter λ = 1. -/
theorem defect_lower_bound (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hsupport : ∀ i j, E i j → kappa ≤ Q i j)
    (u : V → Circle) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (w : V → ℂ) :
    kappa ^ Fintype.card V * (PhaseDefect.delta E u) ^ 2 * ‖w‖ ≤
      128 * (Fintype.card V : ℝ) *
        ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let c : ℂ := (‖w‖ : ℂ)⁻¹
  let v : V → ℂ := c • w
  have hcn : ‖c‖ = ‖w‖⁻¹ := by simp [c, Complex.norm_real]
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, hcn, inv_mul_cancel₀ (ne_of_gt hn)]
  let R := ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖
  have hres (i : V) : ‖(u i : ℂ) * v i - Model.action Q v i‖ ≤ 2 * R / ‖w‖ := by
    have hp := norm_le_pi_norm (phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 v) i
    have hvR : ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) 1 v‖ ≤ 2 * R / ‖w‖ := by
      dsimp [v]
      rw [map_smul, norm_smul, hcn]
      calc
        _ ≤ ‖w‖⁻¹ * (2 * R) := mul_le_mul_of_nonneg_left
          (residual_at_one Q u hQ hrow lam hl0 hl1 w) (inv_nonneg.mpr (le_of_lt hn))
        _ = _ := by ring
    have hh := hp.trans hvR
    simpa [phaseMarkovOperator_apply, Model.action_apply] using hh
  have hphase := BulkPhase.unit_vector_phase_defect E hc Q hQ hrow kappa hk0 hk1
    hsupport u v hv (2 * R / ‖w‖) (by positivity) hres
  have hm := mul_le_mul_of_nonneg_right hphase (le_of_lt hn)
  have hcancel : (64 * (Fintype.card V : ℝ) * (2 * R / ‖w‖)) * ‖w‖ =
      128 * (Fintype.card V : ℝ) * R := by field_simp; ring
  rw [hcancel] at hm
  exact hm

/-- The full phase--Markov coercivity estimate in the defect metric. -/
theorem phase_markov_defect_bound [Nonempty V]
    (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hsupport : ∀ i j, E i j → kappa ≤ Q i j)
    (u : V → Circle) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (w : V → ℂ) :
    max (1 - lam)
      (kappa ^ (2 * Fintype.card V) * (PhaseDefect.delta E u) ^ 2 /
        (128 * (Fintype.card V : ℝ))) * ‖w‖ ≤
      ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
  have hgap := phase_markov_lower_bound Q (fun i => (u i : ℂ)) lam hQ hrow
    (fun i => Circle.norm_coe _) hl0 w
  have hphase := defect_lower_bound E hc Q hQ hrow kappa hk0 hk1 hsupport
    u lam hl0 hl1 w
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hp : kappa ^ (2 * Fintype.card V) ≤ kappa ^ Fintype.card V :=
    pow_le_pow_of_le_one (le_of_lt hk0) hk1 (by omega)
  have hp' := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (sq_nonneg (PhaseDefect.delta E u)) (norm_nonneg w))
  have hphase' : kappa ^ (2 * Fintype.card V) * (PhaseDefect.delta E u) ^ 2 * ‖w‖ ≤
      128 * (Fintype.card V : ℝ) *
        ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by nlinarith
  have hb : (kappa ^ (2 * Fintype.card V) * (PhaseDefect.delta E u) ^ 2 /
      (128 * (Fintype.card V : ℝ))) * ‖w‖ ≤
        ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 128 * (Fintype.card V : ℝ))).mpr
    nlinarith
  rw [max_mul_of_nonneg _ _ (norm_nonneg w)]
  exact max_le hgap hb

/-- The paper's resonance-distance estimate, with its constant depending
only on the support graph. The sole external input is the generic finite
torus error bound, not the Markov estimate itself. -/
theorem phase_markov_distance_bound [Nonempty V]
    (external : BulkTorus.FiniteTorusErrorBound.{u})
    (E : V → V → Prop) (hc : StronglyConnected E) :
    ∃ cE : ℝ, 0 < cE ∧ ∀ (Q : Matrix V V ℝ),
      (∀ i j, 0 ≤ Q i j) → (∀ i, ∑ j, Q i j = 1) →
      ∀ kappa : ℝ, 0 < kappa → kappa ≤ 1 →
      (∀ i j, E i j → kappa ≤ Q i j) →
      ∀ (u : V → Circle) (lam : ℝ), 0 ≤ lam → lam ≤ 1 → ∀ w : V → ℂ,
      max (1 - lam)
        (cE * kappa ^ (2 * Fintype.card V) * (BulkTorus.resonanceDistance E u) ^ 2) * ‖w‖ ≤
        ‖phaseMarkovOperator Q (fun i => (u i : ℂ)) lam w‖ := by
  obtain ⟨C, hC, hdist⟩ := BulkTorus.distance_le_defect E external
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  let cE := (128 * (Fintype.card V : ℝ) * C ^ 2)⁻¹
  refine ⟨cE, by positivity, ?_⟩
  intro Q hQ hrow kappa hk0 hk1 hs u lam hl0 hl1 w
  have hfull := phase_markov_defect_bound E hc Q hQ hrow kappa hk0 hk1 hs
    u lam hl0 hl1 w
  have hdist0 := BulkTorus.resonanceDistance_nonnegative E u
  have hdel0 := PhaseDefect.delta_nonnegative E u
  have hsq : (BulkTorus.resonanceDistance E u) ^ 2 ≤ C ^ 2 * (PhaseDefect.delta E u) ^ 2 := by
    nlinarith [hdist u]
  have hcoef : cE * kappa ^ (2 * Fintype.card V) *
      (BulkTorus.resonanceDistance E u) ^ 2 ≤
        kappa ^ (2 * Fintype.card V) * (PhaseDefect.delta E u) ^ 2 /
          (128 * (Fintype.card V : ℝ)) := by
    have hden : 0 < 128 * (Fintype.card V : ℝ) * C ^ 2 := by positivity
    have hpow : 0 ≤ kappa ^ (2 * Fintype.card V) := by positivity
    have hh := mul_le_mul_of_nonneg_left hsq hpow
    dsimp [cE]
    rw [inv_mul_eq_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have hd0 : (128 * (Fintype.card V : ℝ)) ≠ 0 := by positivity
    field_simp
    nlinarith
  exact (mul_le_mul_of_nonneg_right (max_le_max_left _ hcoef) (norm_nonneg w)).trans hfull

end NonSymmetricDyson.Full.BulkMarkov
