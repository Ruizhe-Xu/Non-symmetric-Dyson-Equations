import Dyson.Full.MainBoundary
import Dyson.Paper.FoundationsPaths

/-! The original M2 zero-set propagation proof: a zero imaginary component
forces all outgoing neighbors to be zero, and actual support walks propagate
this conclusion through an irreducible matrix. No comparison polynomial or
external positivity theorem is used in this argument. -/
noncomputable section
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.BoundaryPropagation
open Full Full.Boundary Full.ExternalAlgebraic
variable {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : ∀ i j, 0 ≤ S i j) (τ : ℝ) (b : Fin n → ℂ)
variable (hb : ∀ i, b i ≠ 0) (hy : ∀ i, 0 ≤ (b i).im)
variable (heq : BasicEstimates.IsDysonSolution S a (τ : ℂ) b)
include a hS τ hb hy heq

theorem zero_along_edge {i j : Fin n} (hij : 0 < S i j) (hi : (b i).im = 0) :
    (b j).im = 0 := by
  have hid := boundary_imaginary_identity S a τ b hb heq i
  rw [hi] at hid
  have hnorm : Complex.normSq (b i) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr (hb i))
  have hsum : (∑ k, S i k * (b k).im) = 0 :=
    (mul_eq_zero.mp hid.symm).resolve_left hnorm
  have hterm := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    mul_nonneg (hS i k) (hy k)) (Finset.mem_univ j)
  rw [hsum] at hterm
  apply le_antisymm _ (hy j)
  by_contra h
  exact (not_lt_of_ge hterm) (mul_pos hij (lt_of_not_ge h))

theorem zero_along_walk {i j : Fin n}
    (p : Resonance.Walk (fun i j => 0 < S i j) i j) :
    (b i).im = 0 → (b j).im = 0 := by
  induction p with
  | nil => exact id
  | cons hij p ih =>
    intro hi
    exact ih (zero_along_edge S a hS τ b hb hy heq hij hi)

theorem all_zero_or_all_positive
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    (∀ i, (b i).im = 0) ∨ (∀ i, 0 < (b i).im) := by
  classical
  have hc := Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr
  by_cases hz : ∃ i, (b i).im = 0
  · obtain ⟨i,hi⟩ := hz
    left
    intro j
    obtain ⟨p⟩ := hc i j
    exact zero_along_walk S a hS τ b hb hy heq p hi
  · right
    intro i
    exact lt_of_le_of_ne (hy i) (fun h => hz ⟨i,h.symm⟩)

theorem positive_iff
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (i j : Fin n) :
    0 < (b i).im ↔ 0 < (b j).im := by
  rcases all_zero_or_all_positive S a hS τ b hb hy heq hirr with hz | hp
  · simp [hz]
  · exact iff_of_true (hp i) (hp j)

omit a hS τ hb hy heq in
/-- The common support conclusion now directly consumes the original
outgoing-edge zero propagation argument. -/
theorem family_regularSupport_eq
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z)) (i j : Fin n) :
    regularSupport m i = regularSupport m j := by
  ext τ
  constructor <;> rintro ⟨hτ,hpos⟩
  · have hb := family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
    exact ⟨hτ,(positive_iff S a hS τ _ hb.1 hb.2.1 hb.2.2 hirr i j).mp hpos⟩
  · have hb := family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
    exact ⟨hτ,(positive_iff S a hS τ _ hb.1 hb.2.1 hb.2.2 hirr j i).mp hpos⟩

end NonSymmetricDyson.Paper.BoundaryPropagation
