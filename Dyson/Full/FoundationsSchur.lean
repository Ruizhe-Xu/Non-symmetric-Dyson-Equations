import Mathlib
import Dyson.BasicEstimates

/-! The domain-safe block Schur-complement argument used in the tree proof.
The block equations and an inverse for the lower block are the hypotheses;
nonvanishing of the Schur complement and the root coordinate are conclusions.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.FoundationsSchur

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem block_schur_complement
    (D G : V →ₗ[ℂ] V) (hGD : G.comp D = LinearMap.id)
    (ℓ : V →ₗ[ℂ] ℂ) (b v : V) (α u : ℂ)
    (hfirst : α * u + ℓ v = 1) (hsecond : D v + u • b = 0) :
    v = -(u • G b) ∧ (α - ℓ (G b)) * u = 1 ∧
      α - ℓ (G b) ≠ 0 ∧ u ≠ 0 := by
  have hGDv : G (D v) = v := by
    simpa using congrArg (fun T : V →ₗ[ℂ] V => T v) hGD
  have hsecond' : v + u • G b = 0 := by
    simpa [hGDv] using congrArg G hsecond
  have hv : v = -(u • G b) := eq_neg_of_add_eq_zero_left hsecond'
  have hscalar : (α - ℓ (G b)) * u = 1 := by
    rw [hv] at hfirst
    simp only [map_neg, map_smul, smul_eq_mul] at hfirst
    linear_combination hfirst
  refine ⟨hv, hscalar, ?_, ?_⟩
  · intro h
    simp [h] at hscalar
  · intro h
    simp [h] at hscalar

/-- The finite coupling calculation uses the same square-root edge weight
in the two directions; no symmetry of the coefficient matrix is needed. -/
theorem square_root_coupling {ι : Type*} [Fintype ι]
    (S : ι → ℝ) (hS : ∀ j, 0 ≤ S j) (m : ι → ℂ) :
    (∑ j, (Real.sqrt (S j) : ℂ) * ((Real.sqrt (S j) : ℂ) * m j)) =
      ∑ j, (S j : ℂ) * m j := by
  apply Finset.sum_congr rfl
  intro j _
  have hs : (Real.sqrt (S j) : ℂ) ^ 2 = (S j : ℂ) := by
    exact_mod_cast Real.sq_sqrt (hS j)
  calc
    _ = (Real.sqrt (S j) : ℂ) ^ 2 * m j := by ring
    _ = _ := by rw [hs]

/-- Once the block calculation identifies the coupling scalar, the reciprocal
Dyson equation follows without ever inverting a possibly zero quantity. -/
theorem dyson_of_schur_equations {ι : Type*} [Fintype ι]
    (S : ι → ι → ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (h : ∀ i, ((a i : ℂ) - z - ∑ j, (S i j : ℂ) * m j) * m i = 1) :
    (∀ i, m i ≠ 0) ∧ BasicEstimates.IsDysonSolution S a z m := by
  have hm : ∀ i, m i ≠ 0 := by
    intro i hi
    simpa [hi] using h i
  refine ⟨hm, fun i => ?_⟩
  have hi := h i
  have hinv : (a i : ℂ) - z - ∑ j, (S i j : ℂ) * m j = (m i)⁻¹ := by
    calc
      _ = 1 / m i := (eq_div_iff (hm i)).mpr hi
      _ = _ := one_div _
  linear_combination hinv

end NonSymmetricDyson.Full.FoundationsSchur
