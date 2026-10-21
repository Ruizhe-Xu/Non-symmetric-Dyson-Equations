import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Finite weighted maximum principle, used for uniqueness of a nonsymmetric
vector Dyson equation.  No spectral-radius conclusion is assumed.
-/

noncomputable section

open scoped BigOperators

namespace NonSymmetricDyson.UniquenessAux

variable {ι : Type*} [Fintype ι]

/-- A nonnegative vector dominated by a nonnegative matrix must vanish when
that matrix strictly contracts some strictly positive weight vector. -/
theorem eq_zero_of_strict_weight
    (A : ι → ι → ℝ) (w u : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hwpos : ∀ i, 0 < w i)
    (hunonneg : ∀ i, 0 ≤ u i)
    (hu : ∀ i, u i ≤ ∑ j, A i j * u j)
    (hw : ∀ i, (∑ j, A i j * w j) < w i) :
    ∀ i, u i = 0 := by
  classical
  intro i
  by_contra hi
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun j => u j / w j)
  let r : ℝ := u k / w k
  have hipos : 0 < u i := lt_of_le_of_ne (hunonneg i) (Ne.symm hi)
  have hrpos : 0 < r := lt_of_lt_of_le (div_pos hipos (hwpos i)) (hk i)
  have hpoint : ∀ j, u j ≤ r * w j := by
    intro j
    exact (div_le_iff₀ (hwpos j)).mp (hk j)
  have heq : u k = r * w k := by
    dsimp only [r]
    exact (div_mul_cancel₀ _ (ne_of_gt (hwpos k))).symm
  have hbound : u k ≤ r * ∑ j, A k j * w j := by
    calc
      u k ≤ ∑ j, A k j * u j := hu k
      _ ≤ ∑ j, A k j * (r * w j) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hpoint j) (hA k j)
      _ = r * ∑ j, A k j * w j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hstrict : r * (∑ j, A k j * w j) < u k := by
    rw [heq]
    exact mul_lt_mul_of_pos_left (hw k) hrpos
  exact (not_lt_of_ge hbound) hstrict

/-- The quantitative inhomogeneous weighted maximum principle.  The uniform
row contraction `A w ≤ q w`, with `q < 1`, controls the response to `f ≤ F w`. -/
theorem bound_of_weighted_contraction
    (A : ι → ι → ℝ) (w u f : ι → ℝ) (q F : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hwpos : ∀ i, 0 < w i)
    (hunonneg : ∀ i, 0 ≤ u i) (hq : q < 1)
    (hu : ∀ i, u i ≤ (∑ j, A i j * u j) + f i)
    (hw : ∀ i, (∑ j, A i j * w j) ≤ q * w i)
    (hf : ∀ i, f i ≤ F * w i) :
    ∀ i, u i ≤ F / (1 - q) * w i := by
  classical
  intro i
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun j => u j / w j)
  let r : ℝ := u k / w k
  have hrnonneg : 0 ≤ r := div_nonneg (hunonneg k) (le_of_lt (hwpos k))
  have hpoint : ∀ j, u j ≤ r * w j := by
    intro j
    exact (div_le_iff₀ (hwpos j)).mp (hk j)
  have heq : u k = r * w k := by
    dsimp only [r]
    exact (div_mul_cancel₀ _ (ne_of_gt (hwpos k))).symm
  have hsum : (∑ j, A k j * u j) ≤ r * ∑ j, A k j * w j := by
    calc
      (∑ j, A k j * u j) ≤ ∑ j, A k j * (r * w j) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hpoint j) (hA k j)
      _ = r * ∑ j, A k j * w j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hbound : u k ≤ (r * q + F) * w k := by
    calc
      u k ≤ (∑ j, A k j * u j) + f k := hu k
      _ ≤ r * (∑ j, A k j * w j) + F * w k := add_le_add hsum (hf k)
      _ ≤ r * (q * w k) + F * w k :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hw k) hrnonneg) _
      _ = (r * q + F) * w k := by ring
  have hrq : r ≤ r * q + F := by
    rw [heq] at hbound
    exact (mul_le_mul_iff_left₀ (hwpos k)).mp hbound
  have hrbound : r ≤ F / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
    nlinarith [hrq]
  exact (hpoint i).trans
    (mul_le_mul_of_nonneg_right hrbound (le_of_lt (hwpos i)))


end NonSymmetricDyson.UniquenessAux
