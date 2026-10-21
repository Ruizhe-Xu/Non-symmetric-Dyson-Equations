import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.UniquenessAux

variable {ι : Type*} [Fintype ι]

/-- Weighted finite Cauchy--Schwarz with geometric mean weights. -/
theorem weighted_sqrt_sum_sq_le (S u v : ι → ℝ)
    (hS : ∀ j, 0 ≤ S j) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    (∑ j, S j * Real.sqrt (u j * v j)) ^ 2 ≤
      (∑ j, S j * u j) * (∑ j, S j * v j) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun j _ => mul_nonneg (hS j) (hu j))
    (fun j _ => mul_nonneg (hS j) (hv j))
  intro j _
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (hu j) (hv j))]
  ring

/-- The positive imaginary part of the spectral parameter makes the geometric
mean of the two imaginary-part equations a strict supersolution. -/
theorem strict_geometric_mean_row (S u v : ι → ℝ)
    (hS : ∀ j, 0 ≤ S j) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (η b c U V : ℝ) (hη : 0 < η) (hb : 0 < b) (hc : 0 < c)
    (hU : U = b ^ 2 * (η + ∑ j, S j * u j))
    (hV : V = c ^ 2 * (η + ∑ j, S j * v j)) :
    b * c * (∑ j, S j * Real.sqrt (u j * v j)) < Real.sqrt (U * V) := by
  have hA : 0 ≤ ∑ j, S j * u j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS j) (hu j)
  have hB : 0 ≤ ∑ j, S j * v j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS j) (hv j)
  have hAB : (∑ j, S j * u j) * (∑ j, S j * v j) <
      (η + ∑ j, S j * u j) * (η + ∑ j, S j * v j) := by
    nlinarith [mul_nonneg (le_of_lt hη) hA, mul_nonneg (le_of_lt hη) hB,
      sq_pos_of_pos hη]
  have hfactor : 0 < b ^ 2 * c ^ 2 := mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc)
  have hCS := weighted_sqrt_sum_sq_le S u v hS hu hv
  apply Real.lt_sqrt_of_sq_lt
  calc
    (b * c * (∑ j, S j * Real.sqrt (u j * v j))) ^ 2 =
        (b ^ 2 * c ^ 2) * (∑ j, S j * Real.sqrt (u j * v j)) ^ 2 := by ring
    _ ≤ (b ^ 2 * c ^ 2) * ((∑ j, S j * u j) * (∑ j, S j * v j)) :=
      mul_le_mul_of_nonneg_left hCS (le_of_lt hfactor)
    _ < (b ^ 2 * c ^ 2) *
        ((η + ∑ j, S j * u j) * (η + ∑ j, S j * v j)) :=
      mul_lt_mul_of_pos_left hAB hfactor
    _ = U * V := by rw [hU, hV]; ring


end NonSymmetricDyson.UniquenessAux
