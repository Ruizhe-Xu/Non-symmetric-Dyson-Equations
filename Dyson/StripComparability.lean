import Dyson.ImaginaryComparability
import Dyson.ComponentBounds

set_option autoImplicit false

/-!
# Imaginary-part comparison on an unbounded vertical strip

The assumption `L/(1+‖z‖) ≤ ‖m_i‖` is an a priori component-modulus
bound, not a comparison of imaginary parts. Splitting into small and large
imaginary parts gives one comparison constant for the whole strip.
-/

noncomputable section

namespace Manuscript.StripComparability

open scoped BigOperators
open Manuscript.ImaginaryComparability
open NonSymmetricDyson.BasicEstimates

/-- A scaled modulus bound is a fixed positive modulus bound below height one. -/
theorem small_height_modulus_lower_bound
    (T L : ℝ) (hT : 0 ≤ T) (z : ℂ) (hznorm : ‖z‖ ≤ T + z.im)
    (hheight : z.im ≤ 1) (w : ℂ) (hlower : L / (1 + ‖z‖) ≤ ‖w‖) :
    L / (T + 2) ≤ ‖w‖ := by
  have hden : 0 < 1 + ‖z‖ := by positivity
  have hprod := (div_le_iff₀ hden).mp hlower
  apply (div_le_iff₀ (by linarith : 0 < T + 2)).mpr
  exact hprod.trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg w))

/-- Above height one, the same scaled bound controls `Im z * |m_i|`. -/
theorem large_height_scaled_modulus_lower_bound
    (T L : ℝ) (hT : 0 ≤ T) (z : ℂ) (hznorm : ‖z‖ ≤ T + z.im)
    (hheight : 1 ≤ z.im) (w : ℂ) (hlower : L / (1 + ‖z‖) ≤ ‖w‖) :
    L / (T + 2) ≤ z.im * ‖w‖ := by
  have hden : 0 < 1 + ‖z‖ := by positivity
  have hprod := (div_le_iff₀ hden).mp hlower
  have hdenbound : 1 + ‖z‖ ≤ z.im * (T + 2) := by
    nlinarith [mul_nonneg hT (sub_nonneg.mpr hheight)]
  apply (div_le_iff₀ (by linarith : 0 < T + 2)).mpr
  have h := hprod.trans (mul_le_mul_of_nonneg_left hdenbound (norm_nonneg w))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- At large height the weighted imaginary-part equation and the modulus
bound give a lower bound for `Im z * Im m_i`. -/
theorem large_height_imaginary_part_lower_bound
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (a : Fin n → ℝ) (T L : ℝ) (hT : 0 ≤ T) (hL : 0 < L)
    (z : ℂ) (hznorm : ‖z‖ ≤ T + z.im) (hheight : 1 ≤ z.im)
    (m : Fin n → ℂ) (hm : IsUpperSolution m) (hsol : IsDysonSolution S a z m)
    (hlower : ∀ i, L / (1 + ‖z‖) ≤ ‖m i‖) (i : Fin n) :
    (L / (T + 2)) ^ 2 ≤ z.im * (m i).im := by
  have hz : 0 < z.im := by linarith
  have hd : 0 < L / (T + 2) := div_pos hL (by linarith)
  have hscaled := large_height_scaled_modulus_lower_bound T L hT z hznorm
    hheight (m i) (hlower i)
  have hsq : (L / (T + 2)) ^ 2 ≤ (z.im * ‖m i‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscaled)
      (add_nonneg hd.le (mul_nonneg hz.le (norm_nonneg (m i))))]
  have hsum : 0 ≤ ∑ j, S i j * (m j).im :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hS i j) (hm j).le)
  have hweight : z.im * ‖m i‖ ^ 2 ≤ (m i).im := by
    have hid := weighted_imaginary_part_identity hm hsol i
    rw [Complex.normSq_eq_norm_sq] at hid
    nlinarith [mul_nonneg (sq_nonneg ‖m i‖) hsum]
  have hmult := mul_le_mul_of_nonneg_left hweight hz.le
  nlinarith

/-- The rough resolvent estimate bounds the total imaginary mass at every height. -/
theorem height_times_total_imaginary_part_le_dimension
    {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (a : Fin n → ℝ) (z : ℂ) (hz : 0 < z.im) (m : Fin n → ℂ)
    (hm : IsUpperSolution m) (hsol : IsDysonSolution S a z m) :
    z.im * (∑ j, (m j).im) ≤ (n : ℝ) := by
  have heach : ∀ j, z.im * (m j).im ≤ 1 := by
    intro j
    have h := (Complex.im_le_norm (m j)).trans (rough_bound hS hz hm hsol j)
    have h' : (m j).im * z.im ≤ 1 :=
      (le_div_iff₀ hz).mp (by simpa only [one_div] using h)
    simpa only [mul_comm] using h'
  rw [Finset.mul_sum]
  calc
    (∑ j, z.im * (m j).im) ≤ ∑ _j : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => heach j)
    _ = (n : ℝ) := by simp

/-- A fixed scaled lower modulus bound gives a uniform imaginary-part
comparison on the entire vertical strip, including arbitrarily large heights.
The comparison constant depends only on `S`, `L`, `T`, and the dimension. -/
theorem dyson_imaginary_parts_comparable_on_strip
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ),
      0 < z.im → |z.re| ≤ T → IsUpperSolution m → IsDysonSolution S a z m →
      (∀ i, L / (1 + ‖z‖) ≤ ‖m i‖) →
        ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  let q : ℝ := (L / (T + 2)) ^ 2
  have hq : 0 < q := sq_pos_of_pos (div_pos hL (by linarith))
  obtain ⟨C₀, hC₀, hsmall⟩ := dyson_imaginary_parts_comparable hn S hS hirr q hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let C : ℝ := min C₀ (q / n)
  have hC : 0 < C := lt_min hC₀ (div_pos hq hnR)
  refine ⟨C, hC, ?_⟩
  intro a z m hz hRe hm hsol hlower i
  have hznorm : ‖z‖ ≤ T + z.im := by
    have hb := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz] at hb
    linarith
  have htotalpos : 0 ≤ ∑ j, (m j).im :=
    Finset.sum_nonneg (fun j _ => (hm j).le)
  by_cases hheight : z.im ≤ 1
  · have hmod : ∀ j, q ≤ Complex.normSq (m j) := by
      intro j
      have hl := small_height_modulus_lower_bound T L hT z hznorm hheight
        (m j) (hlower j)
      have hd : 0 < L / (T + 2) := div_pos hL (by linarith)
      rw [Complex.normSq_eq_norm_sq]
      dsimp only [q]
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hd.le (norm_nonneg (m j)))]
    exact (mul_le_mul_of_nonneg_right (min_le_left C₀ (q / n)) htotalpos).trans
      (hsmall a z m hz.le hm hsol hmod i)
  · have hheight' : 1 ≤ z.im := le_of_lt (lt_of_not_ge hheight)
    have hlow : q ≤ z.im * (m i).im :=
      large_height_imaginary_part_lower_bound S hS a T L hT hL z hznorm
        hheight' m hm hsol hlower i
    have htotal := height_times_total_imaginary_part_le_dimension S hS a z hz m hm hsol
    have hCn : C * (n : ℝ) ≤ q :=
      (le_div_iff₀ hnR).mp (min_le_right C₀ (q / n))
    have hupper := (mul_le_mul_of_nonneg_left htotal hC.le).trans hCn
    have hfin : (C * (∑ j, (m j).im)) * z.im ≤ (m i).im * z.im := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hz).mp (by simpa only [mul_comm] using hfin)

/-- The imaginary-part comparison for actual Dyson solutions follows from
a uniform component norm bound. No imaginary-part comparison or modulus
lower bound is assumed here: the latter is proved from the Dyson equation.
The constant depends only on `S`, `a`, `M`, `T`, and the dimension. -/
theorem dyson_imaginary_parts_comparable_of_uniform_bound
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a : Fin n → ℝ) (M T : ℝ) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (m : Fin n → ℂ),
      0 < z.im → |z.re| ≤ T → IsUpperSolution m → IsDysonSolution S a z m →
      (∀ i, ‖m i‖ ≤ M) →
        ∀ i, C * (∑ j, (m j).im) ≤ (m i).im := by
  let L := NonSymmetricDyson.ComponentBounds.uniformLowerConstant S a M
  have hL : 0 < L :=
    NonSymmetricDyson.ComponentBounds.uniformLowerConstant_pos hS hM
  obtain ⟨C, hC, hcomp⟩ := dyson_imaginary_parts_comparable_on_strip
    hn S hS hirr T L hT hL
  refine ⟨C, hC, ?_⟩
  intro z m hz hRe hm hsol hbound i
  exact hcomp a z m hz hRe hm hsol
    (fun j => NonSymmetricDyson.ComponentBounds.common_scaled_lower_bound
      hS hm hsol hM hbound j) i

end Manuscript.StripComparability
