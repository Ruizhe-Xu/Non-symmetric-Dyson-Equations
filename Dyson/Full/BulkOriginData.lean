import Dyson.Full.BulkPerron
import Dyson.InteriorStability

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkOriginData
universe u
variable {V : Type u} [Fintype V]

def imaginaryVector (q : V → ℝ) : V → ℂ := fun i => (q i : ℂ) * Complex.I
def originMatrix (S : Matrix V V ℝ) (q : V → ℝ) : Matrix V V ℝ :=
  fun i j => q i ^ 2 * S i j

theorem originMatrix_support (S : Matrix V V ℝ) (q : V → ℝ)
    (hq : ∀ i, 0 < q i) (i j : V) :
    0 < originMatrix S q i j ↔ 0 < S i j := by
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos (hq i))

theorem origin_stability (S : Matrix V V ℝ) (q : V → ℝ) :
    InteriorStability.stabilityOperator S (imaginaryVector q) =
      BulkPerron.plusOperator (originMatrix S q) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [InteriorStability.stabilityOperator_apply, imaginaryVector,
    BulkPerron.plusOperator, LinearMap.add_apply, LinearMap.id_apply,
    Pi.add_apply, Model.action_apply, originMatrix, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_pow, Complex.I_sq]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem positive_origin_eigenvector (S : Matrix V V ℝ) (a : V → ℝ) (tau : ℝ)
    (q : V → ℝ) (hq : ∀ i, 0 < q i)
    (hsol : BasicEstimates.IsDysonSolution S a (tau : ℂ) (imaginaryVector q)) :
    ∀ i, ∑ j, originMatrix S q i j * q j = q i := by
  have hm : BasicEstimates.IsUpperSolution (imaginaryVector q) := by
    intro i
    simpa [imaginaryVector, Complex.mul_im] using hq i
  intro i
  have hh := BasicEstimates.weighted_imaginary_part_identity hm hsol i
  have hnorm (j : V) : ‖imaginaryVector q j‖ = q j := by
    simp [imaginaryVector, norm_mul, Complex.norm_real, abs_of_pos (hq j)]
  simp only [imaginaryVector, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, Complex.ofReal_im,
    zero_add, Complex.normSq_eq_norm_sq] at hh
  have hn : ‖(q i : ℂ) * Complex.I‖ = q i := hnorm i
  rw [hn] at hh
  calc
    _ = q i ^ 2 * ∑ j, S i j * q j := by
      simp only [originMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = q i := hh.symm

/-- Deflation data for the actual Dyson stability operator at a purely
imaginary boundary solution, derived from the general Perron principle. -/
theorem actual_origin_kernel_data [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (a : V → ℝ) (tau : ℝ) (q : V → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (hq : ∀ i, 0 < q i)
    (hsol : BasicEstimates.IsDysonSolution S a (tau : ℂ) (imaginaryVector q))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ phi : (V → ℂ) →L[ℂ] ℂ,
      phi (BulkPerron.signMul t (fun i => (q i : ℂ))) = 1 ∧
      phi (BulkPerron.signMul t (fun i => (q i : ℂ) ^ 2)) ≠ 0 ∧
      (∀ x, phi (InteriorStability.stabilityOperator S (imaginaryVector q) x) = 0) ∧
      ∀ x, InteriorStability.stabilityOperator S (imaginaryVector q) x = 0 →
        x = phi x • BulkPerron.signMul t (fun i => (q i : ℂ)) := by
  have hA : ∀ i j, 0 ≤ originMatrix S q i j :=
    fun i j => mul_nonneg (sq_nonneg _) (hS i j)
  have heq : (fun i j => 0 < originMatrix S q i j) = (fun i j => 0 < S i j) := by
    funext i j
    exact propext (originMatrix_support S q hq i j)
  have hcA : Resonance.StronglyConnected (fun i j => 0 < originMatrix S q i j) := by
    rw [heq]
    exact hc
  have hsA (i j : V) (hij : originMatrix S q i j ≠ 0) : t j = -t i := by
    apply hs i j
    intro hz
    apply hij
    simp [originMatrix, hz]
  have hh := BulkPerron.signed_kernel_data_of_perron external (originMatrix S q) hA hcA
    q hq (positive_origin_eigenvector S a tau q hq hsol) t ht hsA
  simpa only [origin_stability] using hh

end NonSymmetricDyson.Full.BulkOriginData
