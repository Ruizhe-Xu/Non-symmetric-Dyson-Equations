import Dyson.Full.BulkMarkov
import Dyson.Full.BulkBoundary

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkSubstochastic
universe u
open MarkovStability
variable {V : Type u} [Fintype V] [Nonempty V]

def completeMatrix (P : Matrix V V ℝ) (d : V → ℝ) : Matrix V V ℝ :=
  fun i j => P i j + if i = j then d i else 0

theorem complete_nonnegative (P : Matrix V V ℝ) (d : V → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hd : ∀ i, 0 ≤ d i) :
    ∀ i j, 0 ≤ completeMatrix P d i j := by
  intro i j
  unfold completeMatrix
  split_ifs
  · exact add_nonneg (hP i j) (hd i)
  · simpa using hP i j

theorem complete_row_sum (P : Matrix V V ℝ) (d : V → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1 - d i) (i : V) :
    ∑ j, completeMatrix P d i j = 1 := by
  simp [completeMatrix, Finset.sum_add_distrib, hrow]

theorem complete_action (P : Matrix V V ℝ) (d : V → ℝ) (w : V → ℂ) :
    Model.action (completeMatrix P d) w =
      Model.action P w + fun i => (d i : ℂ) * w i := by
  funext i
  simp only [Model.action_apply, completeMatrix, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib, Pi.add_apply]
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

theorem substochastic_gap (P : Matrix V V ℝ) (d : V → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1 - d i)
    (d0 : ℝ) (hd0 : 0 ≤ d0) (hd : ∀ i, d0 ≤ d i)
    (u : V → Circle) (w : V → ℂ) :
    d0 * ‖w‖ ≤ ‖phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w‖ := by
  have hsum (i : V) : 0 ≤ 1 - d i := by
    rw [← hrow i]
    exact Finset.sum_nonneg (fun j _ => hP i j)
  have h01 : 0 ≤ 1 - d0 := by
    have h := hsum (Classical.arbitrary V)
    have h' := hd (Classical.arbitrary V)
    linarith
  have hnorm : ‖Model.action P w‖ ≤ (1 - d0) * ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg h01 (norm_nonneg _))).mpr
    intro i
    calc
      _ ≤ ∑ j, ‖(P i j : ℂ) * w j‖ := norm_sum_le _ _
      _ = ∑ j, P i j * ‖w j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        simp [norm_mul, Complex.norm_real, abs_of_nonneg (hP i j)]
      _ ≤ ∑ j, P i j * ‖w‖ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) (hP i j)
      _ = (1 - d i) * ‖w‖ := by rw [← Finset.sum_mul, hrow]
      _ ≤ (1 - d0) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (by linarith [hd i]) (norm_nonneg _)
  have ht := norm_sub_norm_le (phaseMultiply (fun i => (u i : ℂ)) w) (Model.action P w)
  rw [phaseMultiply_norm _ _ (fun i => Circle.norm_coe _)] at ht
  have he : phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w =
      phaseMultiply (fun i => (u i : ℂ)) w - Model.action P w := by
    ext i
    simp [phaseMarkovOperator_apply, phaseMultiply, Model.action_apply]
  rw [he]
  linarith

theorem complete_residual_bound (P : Matrix V V ℝ) (d : V → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1 - d i)
    (d0 C : ℝ) (hd0 : 0 ≤ d0) (hC : 0 ≤ C)
    (hd : ∀ i, d0 ≤ d i) (hdu : ∀ i, d i ≤ C * d0)
    (u : V → Circle) (w : V → ℂ) :
    ‖phaseMarkovOperator (completeMatrix P d) (fun i => (u i : ℂ)) 1 w‖ ≤
      (1 + C) * ‖phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w‖ := by
  have he : phaseMarkovOperator (completeMatrix P d) (fun i => (u i : ℂ)) 1 w =
      phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w -
        (fun i => (d i : ℂ) * w i) := by
    have hh := complete_action P d w
    ext i
    have hi := congrFun hh i
    simp only [phaseMarkovOperator_apply, Complex.ofReal_one, one_mul,
      Model.action_apply, Pi.add_apply] at hi ⊢
    rw [hi]
    simp only [Pi.sub_apply, phaseMarkovOperator_apply, Complex.ofReal_one, one_mul]
    ring
  have hdnon (i : V) : 0 ≤ d i := hd0.trans (hd i)
  have hdiag : ‖fun i => (d i : ℂ) * w i‖ ≤ C * d0 * ‖w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdnon i)]
    exact mul_le_mul (hdu i) (norm_le_pi_norm _ i) (norm_nonneg _) (by positivity)
  have hgap := substochastic_gap P d hP hrow d0 hd0 hd u w
  rw [he]
  calc
    _ ≤ ‖phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w‖ +
        ‖fun i => (d i : ℂ) * w i‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hgap hC]

/-- A nonnegative substochastic matrix has the same quantitative graph
phase estimate when its row deficits are uniformly comparable. -/
theorem phase_distance_bound (external : BulkTorus.FiniteTorusErrorBound.{u})
    (E : V → V → Prop) (hc : Resonance.StronglyConnected E) :
    ∃ cE : ℝ, 0 < cE ∧ ∀ (P : Matrix V V ℝ) (d : V → ℝ),
      (∀ i j, 0 ≤ P i j) → (∀ i, ∑ j, P i j = 1 - d i) →
      ∀ d0 C : ℝ, 0 ≤ d0 → 0 ≤ C →
      (∀ i, d0 ≤ d i) → (∀ i, d i ≤ C * d0) →
      ∀ kappa : ℝ, 0 < kappa → kappa ≤ 1 →
      (∀ i j, E i j → kappa ≤ P i j) →
      ∀ (u : V → Circle) (w : V → ℂ),
        cE * kappa ^ (2 * Fintype.card V) * (BulkTorus.resonanceDistance E u) ^ 2 * ‖w‖ ≤
          (1 + C) * ‖phaseMarkovOperator P (fun i => (u i : ℂ)) 1 w‖ := by
  obtain ⟨cE, hcE, hbound⟩ := BulkMarkov.phase_markov_distance_bound external E hc
  refine ⟨cE, hcE, ?_⟩
  intro P d hP hr d0 C hd0 hC hd hdu kappa hk0 hk1 hs u w
  have hdnon : ∀ i, 0 ≤ d i := fun i => hd0.trans (hd i)
  have hs' (i j : V) (hij : E i j) : kappa ≤ completeMatrix P d i j := by
    apply (hs i j hij).trans
    unfold completeMatrix
    split_ifs <;> linarith [hdnon i]
  have h := hbound (completeMatrix P d) (complete_nonnegative P d hP hdnon)
    (complete_row_sum P d hr) kappa hk0 hk1 hs' u 1 (by norm_num) (by norm_num) w
  have hc0 : 0 ≤ cE * kappa ^ (2 * Fintype.card V) *
      (BulkTorus.resonanceDistance E u) ^ 2 := by positivity
  simp only [sub_self, max_eq_right hc0] at h
  exact h.trans (complete_residual_bound P d hP hr d0 C hd0 hC hd hdu u w)

end NonSymmetricDyson.Full.BulkSubstochastic
