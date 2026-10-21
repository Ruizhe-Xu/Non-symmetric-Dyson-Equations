import Dyson.Full.BulkEuclidean
import Dyson.ComponentBounds

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkInputs
open Resonance
variable {V : Type*} [Fintype V] [Nonempty V]

theorem walk_comparison (E : V → V → Prop) (y : V → ℝ) (k : ℝ)
    (hk : 0 ≤ k) (hedge : ∀ i j, E i j → k * y j ≤ y i)
    {a b : V} (p : Walk E a b) : k ^ BulkShortest.length p * y b ≤ y a := by
  induction p with
  | nil => simp [BulkShortest.length]
  | @cons a b c hab rest ih =>
      have hh := mul_le_mul_of_nonneg_left ih hk
      simp only [BulkShortest.length, pow_succ]
      nlinarith [hedge a b hab]

/-- All quantitative bulk input constants are constructed uniformly from a
bounded actual Dyson solution, bounded spectral parameter, and fixed support.
No comparability hypothesis is left as an assumption of the final application. -/
theorem uniform_data
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hcS : StronglyConnected (fun i j => S i j ≠ 0))
    (M Z : ℝ) (hM : 0 < M) (hZ : 0 ≤ Z) :
    ∃ b c s P R B : ℝ, 0 < b ∧ 0 < c ∧ 0 < s ∧ 0 < P ∧ 0 ≤ R ∧ 0 ≤ B ∧
      (∀ i j, S i j ≠ 0 → s ≤ S i j) ∧ (∀ i, ∑ j, S i j ≤ R) ∧
      ∀ (z : ℂ) (m : V → ℂ), BasicEstimates.IsUpperSolution m →
      BasicEstimates.IsDysonSolution S a z m → 0 ≤ z.im → ‖z‖ ≤ Z →
      (∀ i, ‖m i‖ ≤ M) →
      0 < (∑ i, (m i).im) ∧ (∑ i, (m i).im) ≤ P ∧
      (∀ i, c * (∑ j, (m j).im) ≤ (m i).im) ∧
      (∀ i, (m i).im ≤ ∑ j, (m j).im) ∧
      (∀ i, b ≤ ‖m i‖) ∧ (∀ i, ‖z - (a i : ℂ)‖ ≤ B) := by
  obtain ⟨s, hs, _, hsupport⟩ := BulkKernel.exists_positive_support_bound S
  let b := ComponentBounds.uniformLowerConstant S a M / (1 + Z)
  have hb : 0 < b := div_pos (ComponentBounds.uniformLowerConstant_pos hS hM.le) (by positivity)
  let k := min 1 (b ^ 2 * s)
  have hk : 0 < k := lt_min (by norm_num) (by positivity)
  have hk1 : k ≤ 1 := min_le_left _ _
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  let c := k ^ (Fintype.card V - 1) / (Fintype.card V : ℝ)
  have hc : 0 < c := div_pos (pow_pos hk _) hd
  let P := (Fintype.card V : ℝ) * M
  let R := ∑ i, ∑ j, S i j
  let B := Z + ∑ i, |a i|
  have hsS (i j : V) (h : S i j ≠ 0) : s ≤ S i j :=
    hsupport i j (lt_of_le_of_ne (hS i j) (Ne.symm h))
  have hrow (i : V) : ∑ j, S i j ≤ R :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hS i j) (Finset.mem_univ i)
  refine ⟨b, c, s, P, R, B, hb, hc, hs, mul_pos hd hM,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hS i j), by dsimp [B]; positivity,
    hsS, hrow, ?_⟩
  intro z m hm hsol hz hzN hbound
  let y (i : V) := (m i).im
  have hblo (i : V) : b ≤ ‖m i‖ := by
    have hh := ComponentBounds.common_scaled_lower_bound hS hm hsol hM.le hbound i
    have hden := div_le_div₀ (ComponentBounds.uniformLowerConstant_pos (a := a) hS hM.le).le
      (le_refl (ComponentBounds.uniformLowerConstant S a M)) (by positivity : 0 < 1 + ‖z‖)
      (by linarith : 1 + ‖z‖ ≤ 1 + Z)
    exact hden.trans hh
  have hedge (i j : V) (hij : S i j ≠ 0) : k * y j ≤ y i := by
    have hEq := BasicEstimates.weighted_imaginary_part_identity hm hsol i
    rw [Complex.normSq_eq_norm_sq] at hEq
    have hsum : S i j * y j ≤ ∑ j, S i j * y j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hS i j) (hm j).le) (Finset.mem_univ j)
    have hbq : b ^ 2 ≤ ‖m i‖ ^ 2 := by nlinarith [hblo i, norm_nonneg (m i)]
    have hprod := mul_le_mul hbq (hsS i j hij) hs.le (sq_nonneg ‖m i‖)
    have hlo := (min_le_right (1 : ℝ) (b ^ 2 * s)).trans hprod
    have hh := mul_le_mul_of_nonneg_right hlo (hm j).le
    have hsum' := mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖m i‖)
    dsimp [y] at hh hsum' ⊢
    nlinarith [mul_nonneg (sq_nonneg ‖m i‖) hz]
  have hpair (i j : V) : k ^ (Fintype.card V - 1) * y j ≤ y i := by
    obtain ⟨p, hp⟩ := BulkShortest.connected_short_walk hcS i j
    have hh := walk_comparison (fun i j => S i j ≠ 0) y k hk.le hedge p
    have hpow := pow_le_pow_of_le_one hk.le hk1 (by omega : BulkShortest.length p ≤ Fintype.card V - 1)
    exact (mul_le_mul_of_nonneg_right hpow (hm j).le).trans hh
  have hcompare (i : V) : c * ∑ j, y j ≤ y i := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpair i j)
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    dsimp [c]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  have hr : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hrP : ∑ i, y i ≤ P := by
    calc
      _ ≤ ∑ _i : V, M := Finset.sum_le_sum fun i _ =>
        ((le_abs_self (m i).im).trans (Complex.abs_im_le_norm (m i))).trans (hbound i)
      _ = _ := by simp [P]
  refine ⟨hr, hrP, hcompare, ?_, hblo, ?_⟩
  · intro i
    exact Finset.single_le_sum (fun j _ => (hm j).le) (Finset.mem_univ i)
  · intro i
    have ha := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    have hh := norm_sub_le z (a i : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at hh
    dsimp [B]
    linarith

end NonSymmetricDyson.Full.BulkInputs
