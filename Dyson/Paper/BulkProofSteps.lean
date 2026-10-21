import Dyson.Paper.BulkGraph
import Dyson.Full.BulkAlgebra

/-! Literal intermediate estimates in the manuscript's three-step Markov
proof: the unsquared modulus loss, shortest-path propagation, and the
cycle-product telescoping estimate. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.BulkProofSteps
open Resonance Full
variable {V : Type*} [Fintype V]

/-- The triangle inequality before introducing the loss hᵢ=1−|wᵢ|. -/
theorem row_triangle (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (u : V → Circle) (w : V → ℂ) (lam : ℝ) (hlam : 0 ≤ lam) (i : V) :
    ‖w i‖ ≤ lam * (∑ j, Q i j * ‖w j‖) +
      ‖MarkovStability.phaseMarkovOperator Q (fun j => (u j : ℂ)) lam w‖ := by
  have hs : ‖Model.action Q w i‖ ≤ ∑ j, Q i j * ‖w j‖ := by
    calc
      _ ≤ ∑ j, ‖(Q i j : ℂ)*w j‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simp [norm_mul,Complex.norm_real,abs_of_nonneg (hQ i j)]
  have ht := norm_sub_norm_le ((u i : ℂ)*w i) ((lam : ℂ)*Model.action Q w i)
  rw [norm_mul,Circle.norm_coe,one_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hlam] at ht
  have hr := norm_le_pi_norm (MarkovStability.phaseMarkovOperator Q
    (fun j => (u j : ℂ)) lam w) i
  change ‖(u i : ℂ)*w i-(lam : ℂ)*Model.action Q w i‖ ≤ _ at hr
  have hm := mul_le_mul_of_nonneg_left hs hlam
  linarith

/-- Equation `eq:weighted-h`, with exactly the original unsquared loss. -/
theorem weighted_modulus_loss (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (u : V → Circle) (w : V → ℂ)
    (hw : ‖w‖ = 1) (lam : ℝ) (hlam : (1/2 : ℝ) ≤ lam) (hlam1 : lam ≤ 1)
    (i : V) :
    ∑ j, Q i j * (1-‖w j‖) ≤
      2 * ((1-‖w i‖) + ‖MarkovStability.phaseMarkovOperator Q (fun j => (u j : ℂ)) lam w‖) := by
  have htri := row_triangle Q hQ u w lam (by linarith) i
  have hs : (∑ j, Q i j * (1-‖w j‖)) = 1-∑ j, Q i j*‖w j‖ := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hrow]
  have hnonneg : 0 ≤ ∑ j, Q i j * (1-‖w j‖) := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hQ i j)
    have hj := norm_le_pi_norm w j
    rw [hw] at hj
    linarith
  rw [hs] at hnonneg ⊢
  nlinarith

/-- Equation `eq:edge-h-bound`, without division by the minimum entry. -/
theorem edge_modulus_loss (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (u : V → Circle) (w : V → ℂ)
    (hw : ‖w‖ = 1) (lam : ℝ) (hlam : (1/2 : ℝ) ≤ lam) (hlam1 : lam ≤ 1)
    (κ : ℝ) (i j : V) (hκ : κ ≤ Q i j) :
    κ*(1-‖w j‖) ≤
      2 * ((1-‖w i‖) + ‖MarkovStability.phaseMarkovOperator Q (fun j => (u j : ℂ)) lam w‖) := by
  have hwle (k : V) : 0 ≤ 1-‖w k‖ := by
    have hh := norm_le_pi_norm w k
    rw [hw] at hh
    linarith
  calc
    _ ≤ Q i j * (1-‖w j‖) := mul_le_mul_of_nonneg_right hκ (hwle j)
    _ ≤ ∑ k, Q i k * (1-‖w k‖) :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hQ i k) (hwle k)) (Finset.mem_univ j)
    _ ≤ _ := weighted_modulus_loss Q hQ hrow u w hw lam hlam hlam1 i

/-- Equation `eq:modulus-close-1`: the original shortest-path iteration.
The factor 2^(d−1) is displayed instead of being hidden in C. -/
theorem propagated_modulus_loss (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) (u : V → Circle) (w : V → ℂ)
    (hw : ‖w‖ = 1) (lam : ℝ) (hlam : (1/2 : ℝ) ≤ lam) (hlam1 : lam ≤ 1)
    (κ : ℝ) (hk0 : 0 < κ) (hk1 : κ ≤ 1)
    (hs : ∀ i j, E i j → κ ≤ Q i j) (i : V) :
    κ^(Fintype.card V-1) * (1-‖w i‖) ≤
      2^(Fintype.card V-1) * (Fintype.card V : ℝ) *
        ‖MarkovStability.phaseMarkovOperator Q (fun j => (u j : ℂ)) lam w‖ := by
  let eps := ‖MarkovStability.phaseMarkovOperator Q (fun j => (u j : ℂ)) lam w‖
  have heps : 0 ≤ eps := norm_nonneg _
  obtain ⟨root,hroot⟩ := BulkPhase.exists_norm_maximum w hw
  have hloss (j : V) : 0 ≤ 1-‖w j‖ := by
    have hh := norm_le_pi_norm w j
    rw [hw] at hh
    linarith
  have hedge (j k : V) (hjk : E j k) :
      (κ/2)*(1-‖w k‖) ≤ (1-‖w j‖)+2*(eps/2) := by
    have hh := edge_modulus_loss Q hQ hrow u w hw lam hlam hlam1 κ j k (hs j k hjk)
    change κ*(1-‖w k‖) ≤ 2*((1-‖w j‖)+eps) at hh
    linarith
  have hp := BulkPhase.uniform_loss E hc (fun j => 1-‖w j‖) hloss
    (eps/2) (κ/2) (by positivity) (by positivity) (by linarith) hedge root
    (by dsimp; rw [hroot]; ring) i
  have hm := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ 2^(Fintype.card V-1) by positivity)
  rw [div_pow] at hm
  have heq : (2:ℝ)^(Fintype.card V-1) *
      (κ^(Fintype.card V-1) / 2^(Fintype.card V-1) * (1-‖w i‖)) =
      κ^(Fintype.card V-1)*(1-‖w i‖) := by field_simp
  rw [heq] at hm
  convert hm using 1 <;> ring

/-- A product of unit complex numbers has a Lipschitz telescoping estimate. -/
theorem circle_mul_difference (a b c d : Circle) :
    ‖((a*b : Circle):ℂ)-((c*d : Circle):ℂ)‖ ≤
      ‖(a:ℂ)-(c:ℂ)‖+‖(b:ℂ)-(d:ℂ)‖ := by
  simp only [Circle.coe_mul]
  calc
    _ = ‖((a:ℂ)-(c:ℂ))*(b:ℂ)+(c:ℂ)*((b:ℂ)-(d:ℂ))‖ := by congr 1; ring
    _ ≤ ‖((a:ℂ)-(c:ℂ))*(b:ℂ)‖+‖(c:ℂ)*((b:ℂ)-(d:ℂ))‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul,Circle.norm_coe,mul_one,one_mul]

/-- Edge phase errors accumulate linearly along an actual directed walk. -/
theorem walk_phase_error (E : V → V → Prop) (u γ : V → Circle) (δ : ℝ)
    (hedge : ∀ i j, E i j → ‖(u i:ℂ)-(((γ i)⁻¹*γ j:Circle):ℂ)‖ ≤ δ)
    {a b : V} (p : Walk E a b) :
    ‖((p.weight u : Circle):ℂ)-(((γ a)⁻¹*γ b:Circle):ℂ)‖ ≤ (BulkShortest.length p:ℝ)*δ := by
  induction p with
  | nil a => simp [BulkShortest.length]
  | @cons a b c hab p ih =>
    have hprod : ((γ a)⁻¹*γ b)*((γ b)⁻¹*γ c) = (γ a)⁻¹*γ c := by group
    calc
      _ = ‖((u a*p.weight u:Circle):ℂ)-((((γ a)⁻¹*γ b)*((γ b)⁻¹*γ c):Circle):ℂ)‖ := by
        rw [hprod]; rfl
      _ ≤ ‖(u a:ℂ)-(((γ a)⁻¹*γ b:Circle):ℂ)‖+
          ‖((p.weight u : Circle):ℂ)-(((γ b)⁻¹*γ c:Circle):ℂ)‖ := circle_mul_difference ..
      _ ≤ δ+(BulkShortest.length p:ℝ)*δ := add_le_add (hedge a b hab) ih
      _ = _ := by simp only [BulkShortest.length,Nat.cast_add,Nat.cast_one]; ring

/-- Equation `eq.u-cycle-bound`; the bound applies to every directed cycle,
and hence to each simple cycle used in the integer lattice. -/
theorem cycle_phase_error (E : V → V → Prop) (u γ : V → Circle) (δ : ℝ)
    (hedge : ∀ i j, E i j → ‖(u i:ℂ)-(((γ i)⁻¹*γ j:Circle):ℂ)‖ ≤ δ)
    (a : V) (p : Walk E a a) :
    ‖((p.weight u : Circle):ℂ)-1‖ ≤ (BulkShortest.length p:ℝ)*δ := by
  simpa using walk_phase_error E u γ δ hedge p

/-- Equation `eq:B-conjugation` in its exact coordinate form. -/
theorem perron_markov_conjugation (F : Matrix V V ℝ) (r : V → ℝ)
    (lam : ℝ) (hr : ∀ i, 0 < r i) (hlam : 0 < lam) (u x : V → ℂ) (i : V) :
    (r i:ℂ)*MarkovStability.phaseMarkovOperator
      (BulkAlgebra.normalizedMarkov F r lam) u lam (fun j => x j/(r j:ℂ)) i =
      u i*x i-Model.action F x i :=
  BulkAlgebra.normalizedMarkov_conjugation F r lam (fun i => (hr i).ne') hlam.ne' u x i

/-- The period-two support relation is an actual anticommutation identity. -/
theorem period_two_anticommutation (S : Matrix V V ℝ) (t : V → ℂ)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) (x : V → ℂ) :
    Model.action S (fun i => t i*x i) = fun i => -t i*Model.action S x i := by
  funext i
  exact BulkAlgebra.action_anticommutes_of_support S t hs x i

end NonSymmetricDyson.Paper.BulkProofSteps
