import Dyson.Full.PerronExistence
import Dyson.ImaginaryComparability

noncomputable section
open scoped BigOperators Matrix
namespace NonSymmetricDyson.Full.Singularities
open Manuscript.PositivityCorrection Manuscript.ImaginaryComparability

/-- A positive eigenvector bounds its eigenvalue by a fixed total-entry
bound. This estimate does not assume symmetry or aperiodicity. -/
theorem positive_eigenvalue_upper {n : ℕ} (hn : 0 < n)
    (A S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (b : ℝ) (hb : 0 ≤ b) (hA : ∀ i j, A i j ≤ b * S i j)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (lam : ℝ)
    (heig : ∀ i, ∑ j, A i j * r j = lam * r i) :
    lam ≤ (n : ℝ) * b * (∑ i, ∑ j, S i j) := by
  classical
  let T : ℝ := ∑ i, ∑ j, S i j
  have hTij (i j : Fin n) : S i j ≤ T := by
    exact (Finset.single_le_sum (fun k _ => hS i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun j _ => hS k j) (Finset.mem_univ i))
  have hsum : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have htotal : lam * (∑ i, r i) ≤ ((n : ℝ) * b * T) * ∑ i, r i := by
    calc
      lam * (∑ i, r i) = ∑ i, ∑ j, A i j * r j := by simp_rw [Finset.mul_sum, heig]
      _ ≤ ∑ i : Fin n, ∑ j, (b * T) * r j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right ((hA i j).trans (mul_le_mul_of_nonneg_left (hTij i j) hb)) (hr j).le
      _ = ((n : ℝ) * b * T) * ∑ i, r i := by
        simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact (mul_le_mul_right hsum).mp htotal

/-- Uniform coordinate comparison for every positive Perron vector of a
matrix in a fixed entrywise order interval. The corrected positive-power
polynomial includes its identity term through the checked supersolution
comparison theorem. -/
theorem uniform_perron_coordinate_comparison {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ c > 0, ∀ (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (lam : ℝ),
      (∀ i j, a * S i j ≤ A i j) → (∀ i j, A i j ≤ b * S i j) →
      (∀ i, 0 < r i) → (∀ i, ∑ j, A i j * r j = lam * r i) →
      ∀ i, c * (∑ j, r j) ≤ r i := by
  let U : ℝ := 1 + (n : ℝ) * b * (∑ i, ∑ j, S i j)
  have hU : 0 < U := by
    have hh : 0 ≤ (n : ℝ) * b * (∑ i, ∑ j, S i j) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hb.le)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hS i j)
    dsimp [U]
    linarith
  let B : Matrix (Fin n) (Fin n) ℝ := (a / U) • S
  have hB : Nonnegative B := fun i j => mul_nonneg (div_pos ha hU).le (hS i j)
  have hBirr : Manuscript.PositivityCorrection.Irreducible B :=
    irreducible_pos_smul S hirr (a / U) (div_pos ha hU)
  obtain ⟨c, hc, hcomp⟩ := irreducible_supersolution_comparability hn B hB hBirr
  refine ⟨c, hc, ?_⟩
  intro A r lam hlo hhi hr heig
  apply hcomp r (fun i => (hr i).le)
  intro i
  have hlu : lam ≤ U := (positive_eigenvalue_upper hn A S hS b hb.le hhi r hr lam heig).trans (by dsimp [U]; linarith)
  have hsum : a * ∑ j, S i j * r j ≤ U * r i := by
    calc
      a * ∑ j, S i j * r j = ∑ j, (a * S i j) * r j := by rw [Finset.mul_sum]; ring_nf
      _ ≤ ∑ j, A i j * r j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlo i j) (hr j).le
      _ = lam * r i := heig i
      _ ≤ U * r i := mul_le_mul_of_nonneg_right hlu (hr i).le
  change (∑ j, (a / U * S i j) * r j) ≤ r i
  have he : (∑ j, (a / U * S i j) * r j) = (a * ∑ j, S i j * r j) / U := by
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact (div_le_iff₀ hU).mpr (by simpa only [mul_comm U] using hsum)

/-- Irreducibility in the manuscript's positive-power sense is preserved by
transpose, so the same coordinate comparison applies to left Perron vectors. -/
theorem irreducible_transpose {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    Manuscript.PositivityCorrection.Irreducible S.transpose := by
  intro i j
  obtain ⟨k, hk, hh⟩ := hirr j i
  refine ⟨k, hk, ?_⟩
  simpa only [← Matrix.transpose_pow, Matrix.transpose_apply] using hh

/-- Euclidean normalization and the left/right pairing turn coordinate
comparison into uniform positive lower and upper bounds. -/
theorem normalized_perron_bounds {n : ℕ} (hn : 0 < n)
    (r l : Fin n → ℝ) (hr : ∀ i, 0 < r i) (hl : ∀ i, 0 < l i)
    (hnorm : ∑ i, r i ^ 2 = 1) (hpair : ∑ i, l i * r i = 1)
    (cr cl : ℝ) (hcr : 0 < cr) (hcl : 0 < cl)
    (hrcomp : ∀ i, cr * ∑ j, r j ≤ r i)
    (hlcomp : ∀ i, cl * ∑ j, l j ≤ l i) :
    (∀ i, cr ≤ r i ∧ r i ≤ 1) ∧ (∀ i, cl ≤ l i ∧ l i ≤ 1 / cr) := by
  classical
  have hrle (i : Fin n) : r i ≤ 1 := by
    have hh : r i ^ 2 ≤ 1 := by
      rw [← hnorm]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_univ i)
    nlinarith [hr i]
  have hsumr : 1 ≤ ∑ i, r i := by
    rw [← hnorm]
    exact Finset.sum_le_sum fun i _ => by nlinarith [hr i, hrle i]
  have hrlow (i : Fin n) : cr ≤ r i := by
    have hh := mul_le_mul_of_nonneg_left hsumr hcr.le
    simpa only [mul_one] using hh.trans (hrcomp i)
  have hsuml : 1 ≤ ∑ i, l i := by
    rw [← hpair]
    exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hl i).le (hrle i)
  have hsumlu : cr * (∑ i, l i) ≤ 1 := by
    rw [← hpair, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrlow i) (hl i).le
  refine ⟨fun i => ⟨hrlow i, hrle i⟩, fun i => ⟨?_, ?_⟩⟩
  · have hh := mul_le_mul_of_nonneg_left hsuml hcl.le
    simpa only [mul_one] using hh.trans (hlcomp i)
  · apply (le_div_iff₀ hcr).mpr
    calc
      l i * cr ≤ (∑ j, l j) * cr := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => (hl j).le) (Finset.mem_univ i)) hcr.le
      _ ≤ 1 := by simpa only [mul_comm] using hsumlu

/-- A nonempty irreducible nonnegative matrix has a positive support edge;
the positive-power definition also handles the one-dimensional case. -/
theorem irreducible_exists_positive_entry {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) : ∃ i j, 0 < S i j := by
  by_contra hh
  push_neg at hh
  have hz : S = 0 := by ext i j; exact le_antisymm (hh i j) (hS i j)
  obtain ⟨k, hk, hp⟩ := hirr ⟨0, hn⟩ ⟨0, hn⟩
  rw [hz, zero_pow (by omega : k ≠ 0)] at hp
  simp at hp

/-- Uniform positive left/right coordinate and eigenvalue bounds on an
entrywise interval of irreducible matrices. The right normalization is
exactly the ordinary Euclidean normalization Σrᵢ²=1. -/
theorem uniform_perron_bounds {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ cr > 0, ∃ cl > 0, ∃ L > 0, ∃ U > 0,
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (r l : Fin n → ℝ) (lam : ℝ),
        (∀ i j, a * S i j ≤ A i j) → (∀ i j, A i j ≤ b * S i j) →
        (∀ i, 0 < r i) → (∀ i, 0 < l i) →
        (∀ i, ∑ j, A i j * r j = lam * r i) →
        (∀ j, ∑ i, l i * A i j = lam * l j) →
        (∑ i, r i ^ 2 = 1) → (∑ i, l i * r i = 1) →
        (∀ i, cr ≤ r i ∧ r i ≤ 1) ∧ (∀ i, cl ≤ l i ∧ l i ≤ 1 / cr) ∧
          L ≤ lam ∧ lam ≤ U := by
  obtain ⟨cr, hcr, hrcomp⟩ := uniform_perron_coordinate_comparison hn S hS hirr a b ha hb
  obtain ⟨cl, hcl, hlcomp⟩ := uniform_perron_coordinate_comparison hn S.transpose
    (fun i j => hS j i) (irreducible_transpose S hirr) a b ha hb
  obtain ⟨i₀, j₀, hentry⟩ := irreducible_exists_positive_entry hn S hS hirr
  let L : ℝ := a * S i₀ j₀ * cr
  let U : ℝ := 1 + (n : ℝ) * b * (∑ i, ∑ j, S i j)
  have hL : 0 < L := mul_pos (mul_pos ha hentry) hcr
  have hU : 0 < U := by
    have hh : 0 ≤ (n : ℝ) * b * (∑ i, ∑ j, S i j) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hb.le)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hS i j)
    dsimp [U]
    linarith
  refine ⟨cr, hcr, cl, hcl, L, hL, U, hU, ?_⟩
  intro A r l lam hlo hhi hr hl hright hleft hnorm hpair
  have hrC := hrcomp A r lam hlo hhi hr hright
  have hlC := hlcomp A.transpose l lam (fun i j => hlo j i) (fun i j => hhi j i) hl
    (fun i => by simpa only [Matrix.transpose_apply, mul_comm] using hleft i)
  have hbounds := normalized_perron_bounds hn r l hr hl hnorm hpair cr cl hcr hcl hrC hlC
  have hA : Nonnegative A := fun i j => (mul_nonneg ha.le (hS i j)).trans (hlo i j)
  have hloL : L ≤ lam * r i₀ := by
    calc
      L ≤ (a * S i₀ j₀) * r j₀ :=
        mul_le_mul_of_nonneg_left (hbounds.1 j₀).1 (mul_pos ha hentry).le
      _ ≤ A i₀ j₀ * r j₀ := mul_le_mul_of_nonneg_right (hlo i₀ j₀) (hr j₀).le
      _ ≤ ∑ j, A i₀ j * r j := Finset.single_le_sum
        (fun j _ => mul_nonneg (hA i₀ j) (hr j).le) (Finset.mem_univ j₀)
      _ = lam * r i₀ := hright i₀
  have hlamp : 0 < lam := (mul_pos_iff_of_pos_right (hr i₀)).mp (hL.trans_le hloL)
  refine ⟨hbounds.1, hbounds.2, hloL.trans (mul_le_of_le_one_right hlamp.le (hbounds.1 i₀).2), ?_⟩
  exact (positive_eigenvalue_upper hn A S hS b hb.le hhi r hr lam hright).trans (by dsimp [U]; linarith)

/-- The paper's uniform Perron bounds for the actual saturated matrices.
Here `scale=1+|z|` in the application; the hypotheses are exactly the already
proved two-sided component-modulus bounds. In particular λ is comparable to
`scale⁻²`, with one pair of constants throughout the region. -/
theorem uniform_saturated_perron_bounds {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ cr > 0, ∃ cl > 0, ∃ L > 0, ∃ U > 0,
      ∀ (scale : ℝ) (m : Fin n → ℂ) (r l : Fin n → ℝ) (lam : ℝ),
        0 < scale → (∀ i, c ≤ scale * ‖m i‖) → (∀ i, scale * ‖m i‖ ≤ C) →
        (∀ i, 0 < r i) → (∀ i, 0 < l i) →
        (∀ i, ∑ j, saturatedMatrix S m i j * r j = lam * r i) →
        (∀ j, ∑ i, l i * saturatedMatrix S m i j = lam * l j) →
        (∑ i, r i ^ 2 = 1) → (∑ i, l i * r i = 1) →
        (∀ i, cr ≤ r i ∧ r i ≤ 1) ∧ (∀ i, cl ≤ l i ∧ l i ≤ 1 / cr) ∧
          L / scale ^ 2 ≤ lam ∧ lam ≤ U / scale ^ 2 := by
  obtain ⟨cr, hcr, cl, hcl, L, hL, U, hU, hall⟩ :=
    uniform_perron_bounds hn S hS hirr (c ^ 2) (C ^ 2) (sq_pos_of_pos hc) (sq_pos_of_pos hC)
  refine ⟨cr, hcr, cl, hcl, L, hL, U, hU, ?_⟩
  intro scale m r l lam hscale hlo hhi hr hl hright hleft hnorm hpair
  let A : Matrix (Fin n) (Fin n) ℝ := (scale ^ 2) • saturatedMatrix S m
  have hentry (i j : Fin n) : A i j = (scale * ‖m i‖) * S i j * (scale * ‖m j‖) := by
    dsimp [A, saturatedMatrix]
    ring
  have hloA : ∀ i j, c ^ 2 * S i j ≤ A i j := by
    intro i j
    rw [hentry]
    calc
      c ^ 2 * S i j = c * S i j * c := by ring
      _ ≤ (scale * ‖m i‖) * S i j * (scale * ‖m j‖) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hlo i) (hS i j)) (hlo j)
          hc.le (mul_nonneg (mul_nonneg hscale.le (norm_nonneg _)) (hS i j))
  have hhiA : ∀ i j, A i j ≤ C ^ 2 * S i j := by
    intro i j
    rw [hentry]
    calc
      (scale * ‖m i‖) * S i j * (scale * ‖m j‖) ≤ C * S i j * C := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hhi i) (hS i j)) (hhi j)
          (mul_nonneg hscale.le (norm_nonneg _)) (mul_nonneg hC.le (hS i j))
      _ = C ^ 2 * S i j := by ring
  have hrightA (i : Fin n) : ∑ j, A i j * r j = (scale ^ 2 * lam) * r i := by
    simp only [A, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hright]
  have hleftA (j : Fin n) : ∑ i, l i * A i j = (scale ^ 2 * lam) * l j := by
    calc
      _ = scale ^ 2 * ∑ i, l i * saturatedMatrix S m i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [A]
        ring
      _ = (scale ^ 2 * lam) * l j := by rw [hleft]; ring
  obtain ⟨hR, hL', hlamlo, hlamhi⟩ :=
    hall A r l (scale ^ 2 * lam) hloA hhiA hr hl hrightA hleftA hnorm hpair
  refine ⟨hR, hL', (div_le_iff₀ (sq_pos_of_pos hscale)).mpr ?_,
    (le_div_iff₀ (sq_pos_of_pos hscale)).mpr ?_⟩
  · simpa only [mul_comm] using hlamlo
  · simpa only [mul_comm] using hlamhi

/-- Positive Perron vectors can be put into the manuscript's simultaneous
Euclidean-right and dual-pairing normalization without changing either
eigenvalue equation. -/
theorem perron_euclidean_normalization {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (r l : Fin n → ℝ) (lam : ℝ)
    (hr : ∀ i, 0 < r i) (hl : ∀ i, 0 < l i)
    (hright : ∀ i, ∑ j, A i j * r j = lam * r i)
    (hleft : ∀ j, ∑ i, l i * A i j = lam * l j)
    (hpair : ∑ i, l i * r i = 1) :
    ∃ R L : Fin n → ℝ, (∀ i, 0 < R i) ∧ (∀ i, 0 < L i) ∧
      (∀ i, ∑ j, A i j * R j = lam * R i) ∧
      (∀ j, ∑ i, L i * A i j = lam * L j) ∧
      (∑ i, R i ^ 2 = 1) ∧ (∑ i, L i * R i = 1) := by
  classical
  let d : ℝ := Real.sqrt (∑ i, r i ^ 2)
  have hsum : 0 < ∑ i, r i ^ 2 := Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
  have hd : 0 < d := Real.sqrt_pos.mpr hsum
  have hdsq : d ^ 2 = ∑ i, r i ^ 2 := Real.sq_sqrt hsum.le
  refine ⟨fun i => r i / d, fun i => d * l i,
    fun i => div_pos (hr i) hd, fun i => mul_pos hd (hl i), ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [← mul_div_assoc, ← Finset.sum_div, hright]
  · intro j
    simp only [mul_assoc, ← Finset.mul_sum, hleft]
    ring
  · simp only [div_pow, ← Finset.sum_div, hdsq]
    exact div_self hsum.ne'
  · rw [← hpair]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hd.ne']

end NonSymmetricDyson.Full.Singularities
