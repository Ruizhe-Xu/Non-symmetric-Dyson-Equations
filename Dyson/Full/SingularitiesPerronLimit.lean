import Dyson.Full.Singularities
import Dyson.BasicEstimates
import Dyson.Full.BoundarySequences

noncomputable section
open Filter
open scoped Topology BigOperators

namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A positive left Perron vector identifies the limiting eigenvalue from
positive normalized fixed vectors of the approximating matrices. Every
estimate is finite dimensional; no spectral-radius continuity is assumed. -/
theorem perron_one_of_approximating_fixed_vectors
    (F₀ : ι → ι → ℝ) (F : ℕ → ι → ι → ℝ)
    (l : ι → ℝ) (lam : ℝ) (v : ℕ → ι → ℝ)
    (hl : ∀ i, 0 < l i)
    (hleft : ∀ j, ∑ i, l i * F₀ i j = lam * l j)
    (hv : ∀ n i, 0 ≤ v n i) (hvsum : ∀ n, ∑ i, v n i = 1)
    (hfixed : ∀ n i, ∑ j, F n i j * v n j = v n i)
    (hconv : ∀ i j, Tendsto (fun n => F n i j) atTop (𝓝 (F₀ i j))) :
    lam = 1 := by
  classical
  let d : ℝ := Finset.univ.inf' Finset.univ_nonempty l
  have hd : 0 < d := (Finset.lt_inf'_iff _).mpr (fun i _ => hl i)
  have hdl (i : ι) : d ≤ l i := Finset.inf'_le l (Finset.mem_univ i)
  have hvle (n : ℕ) (i : ι) : v n i ≤ 1 := by
    rw [← hvsum n]
    exact Finset.single_le_sum (fun j _ => hv n j) (Finset.mem_univ i)
  let P : ℕ → ℝ := fun n => ∑ i, l i * v n i
  have hP (n : ℕ) : d ≤ P n := by
    calc
      d = ∑ i, d * v n i := by rw [← Finset.mul_sum, hvsum, mul_one]
      _ ≤ P n := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hdl i) (hv n i)
  let E : ℕ → ℝ := fun n => ∑ i, ∑ j, l i * |F₀ i j - F n i j|
  have hE : Tendsto E atTop (𝓝 0) := by
    have hh : Tendsto E atTop (𝓝 (∑ i : ι, ∑ j : ι, l i * |F₀ i j - F₀ i j|)) :=
      tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
        tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hconv i j)).abs)
    simpa using hh
  have hidentity (n : ℕ) : (lam - 1) * P n =
      ∑ i, ∑ j, l i * (F₀ i j - F n i j) * v n j := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    have h₀ : ∑ i, ∑ j, l i * F₀ i j * v n j = lam * P n := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hleft, mul_assoc]
      exact (Finset.mul_sum ..).symm
    have hn : ∑ i, ∑ j, l i * F n i j * v n j = P n := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hfixed]
      rfl
    rw [h₀, hn]
    ring
  have hbound (n : ℕ) : |lam - 1| * d ≤ E n := by
    calc
      |lam - 1| * d ≤ |lam - 1| * P n := mul_le_mul_of_nonneg_left (hP n) (abs_nonneg _)
      _ = |(lam - 1) * P n| := by rw [abs_mul, abs_of_nonneg (le_trans hd.le (hP n))]
      _ ≤ ∑ i, ∑ j, |l i * (F₀ i j - F n i j) * v n j| := by
        rw [hidentity]
        exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs ..)
      _ ≤ E n := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul, abs_of_pos (hl i), abs_of_nonneg (hv n j)]
        exact mul_le_of_le_one_right (mul_nonneg (hl i).le (abs_nonneg _)) (hvle n j)
  have hz : |lam - 1| * d ≤ 0 := ge_of_tendsto hE (Filter.Eventually.of_forall hbound)
  have ha : |lam - 1| = 0 := by nlinarith [abs_nonneg (lam - 1)]
  exact sub_eq_zero.mp (abs_eq_zero.mp ha)

/-- At a real energy, the imaginary part of the actual Dyson solution gives
a strictly positive fixed vector of the actual saturated self-energy matrix. -/
theorem real_dyson_positive_fixed_vector
    (S : ι → ι → ℝ) (a : ι → ℝ) (τ : ℝ) (m : ι → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution S a (τ : ℂ) m) :
    (∀ i, 0 < (m i).im / ‖m i‖) ∧
    ∀ i, ∑ j, (‖m i‖ * S i j * ‖m j‖) * ((m j).im / ‖m j‖) =
      (m i).im / ‖m i‖ := by
  have hn (i : ι) : 0 < ‖m i‖ := norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)
  refine ⟨fun i => div_pos (hm i) (hn i), fun i => ?_⟩
  have hi := BasicEstimates.imaginary_part_identity_sq_norm heq i
  simp only [Complex.ofReal_im, zero_add] at hi
  calc
    ∑ j, (‖m i‖ * S i j * ‖m j‖) * ((m j).im / ‖m j‖) =
        ‖m i‖ * ∑ j, S i j * (m j).im := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [(hn j).ne']
    _ = (m i).im / ‖m i‖ := by rw [← hi]; field_simp

/-- Normalization of the actual positive fixed vectors gives the finite
simplex required by the limiting argument. -/
theorem boundary_sequence_perron_one
    (S : ι → ι → ℝ) (a : ι → ℝ) (E : ℕ → ℝ)
    (m : ℕ → ι → ℂ) (m₀ : ι → ℂ) (l : ι → ℝ) (lam : ℝ)
    (hl : ∀ i, 0 < l i)
    (hleft : ∀ j, ∑ i, l i * (‖m₀ i‖ * S i j * ‖m₀ j‖) = lam * l j)
    (hm : ∀ n, BasicEstimates.IsUpperSolution (m n))
    (heq : ∀ n, BasicEstimates.IsDysonSolution S a (E n : ℂ) (m n))
    (hlim : Tendsto m atTop (𝓝 m₀)) : lam = 1 := by
  classical
  let v : ℕ → ι → ℝ := fun n i => (m n i).im / ‖m n i‖
  have hv (n : ℕ) : (∀ i, 0 < v n i) ∧
      ∀ i, ∑ j, (‖m n i‖ * S i j * ‖m n j‖) * v n j = v n i :=
    real_dyson_positive_fixed_vector S a (E n) (m n) (hm n) (heq n)
  let Z : ℕ → ℝ := fun n => ∑ i, v n i
  have hZ (n : ℕ) : 0 < Z n :=
    Finset.sum_pos (fun i _ => (hv n).1 i) Finset.univ_nonempty
  apply perron_one_of_approximating_fixed_vectors
    (fun i j => ‖m₀ i‖ * S i j * ‖m₀ j‖)
    (fun n i j => ‖m n i‖ * S i j * ‖m n j‖) l lam
    (fun n i => v n i / Z n) hl hleft
  · exact fun n i => (div_pos ((hv n).1 i) (hZ n)).le
  · intro n
    rw [← Finset.sum_div]
    exact div_self (hZ n).ne'
  · intro n i
    simp only [← mul_div_assoc, ← Finset.sum_div, (hv n).2]
  · intro i j
    exact (((tendsto_pi_nhds.mp hlim i).norm).mul tendsto_const_nhds).mul
      ((tendsto_pi_nhds.mp hlim j).norm)

/-- At an actual regular frontier point, every positive left Perron
eigenvector of the limiting saturated matrix has eigenvalue one. The
positive support sequence and all Dyson equations are constructed internally. -/
theorem regular_frontier_perron_one {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) (l : Fin n → ℝ) (lam : ℝ)
    (hl : ∀ j, 0 < l j)
    (hleft : ∀ j, ∑ k, l k *
      (‖Boundary.boundaryVector m (τ : ℂ) k‖ * S k j *
        ‖Boundary.boundaryVector m (τ : ℂ) j‖) = lam * l j) : lam = 1 := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨E, _, _, hpos, hsol, ht⟩ :=
    Boundary.regular_frontier_sequence hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  exact boundary_sequence_perron_one S a E
    (fun k => Boundary.boundaryVector m (E k : ℂ))
    (Boundary.boundaryVector m (τ : ℂ)) l lam hl hleft hpos hsol ht

end NonSymmetricDyson.Full.Singularities
