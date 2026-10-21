import Dyson.Model
import Dyson.WeightedMaximum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Interior invertibility of the Dyson stability operator

For any upper-half-plane solution at Im z > 0, the linearized operator
I - diag(m²) S is bijective. No symmetry, irreducibility, or assumed
spectral-radius bound is used. The proof derives a strict positive-weight
contraction directly from the imaginary-part identity of the Dyson equation.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.InteriorStability

variable {ι : Type*} [Fintype ι]

/-- The complex-linear Dyson stability operator `I - diag(m²) S`. -/
def stabilityOperator (S : Matrix ι ι ℝ) (m : ι → ℂ) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun := DysonPaper.Algebra.stabilityAction m (Model.action S)
  map_add' u v := by
    ext i
    simp only [DysonPaper.Algebra.stabilityAction, map_add, Pi.add_apply]
    ring
  map_smul' c u := by
    ext i
    simp only [DysonPaper.Algebra.stabilityAction, map_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem stabilityOperator_apply (S : Matrix ι ι ℝ)
    (m u : ι → ℂ) (i : ι) :
    stabilityOperator S m u i = u i - m i ^ 2 * ∑ j, (S i j : ℂ) * u j := rfl

variable {S : Matrix ι ι ℝ} {a : ι → ℝ} {z : ℂ} {m : ι → ℂ}

/-- The imaginary-part vector is a strict positive contraction weight for
`diag(|m|²) S` whenever `Im z > 0`. -/
theorem imaginary_weight_strict (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    (∑ j, (‖m i‖ ^ 2 * S i j) * (m j).im) < (m i).im := by
  have hnorm : 0 < ‖m i‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)) 2
  have hid := BasicEstimates.weighted_imaginary_part_identity hm hsol i
  rw [Complex.normSq_eq_norm_sq] at hid
  calc
    (∑ j, (‖m i‖ ^ 2 * S i j) * (m j).im) =
        ‖m i‖ ^ 2 * ∑ j, S i j * (m j).im := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ < ‖m i‖ ^ 2 * (z.im + ∑ j, S i j * (m j).im) :=
      mul_lt_mul_of_pos_left (lt_add_of_pos_left _ hz) hnorm
    _ = (m i).im := hid.symm

/-- A vector in the kernel is dominated componentwise by `diag(|m|²) S`
acting on its componentwise norms. -/
theorem kernel_norm_majorant (hS : ∀ i j, 0 ≤ S i j)
    {u : ι → ℂ} (hu : stabilityOperator S m u = 0) (i : ι) :
    ‖u i‖ ≤ ∑ j, (‖m i‖ ^ 2 * S i j) * ‖u j‖ := by
  have hui : u i = m i ^ 2 * ∑ j, (S i j : ℂ) * u j := by
    have h := congrFun hu i
    exact sub_eq_zero.mp h
  calc
    ‖u i‖ = ‖m i‖ ^ 2 * ‖∑ j, (S i j : ℂ) * u j‖ := by
      rw [hui, norm_mul, norm_pow]
    _ ≤ ‖m i‖ ^ 2 * ∑ j, ‖(S i j : ℂ) * u j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
    _ = ∑ j, (‖m i‖ ^ 2 * S i j) * ‖u j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i j)]
      ring

/-- The interior Dyson stability operator has trivial kernel. -/
theorem stability_kernel_trivial (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    {u : ι → ℂ} (hu : stabilityOperator S m u = 0) : u = 0 := by
  have hzero := UniquenessAux.eq_zero_of_strict_weight
    (fun i j => ‖m i‖ ^ 2 * S i j) (fun i => (m i).im) (fun i => ‖u i‖)
    (fun i j => mul_nonneg (sq_nonneg _) (hS i j)) hm (fun i => norm_nonneg _)
    (kernel_norm_majorant hS hu) (imaginary_weight_strict hz hm hsol)
  ext i
  exact norm_eq_zero.mp (hzero i)

/-- The actual linearized stability operator is injective for every interior
upper-half-plane Dyson solution. -/
theorem stability_injective (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) :
    Function.Injective (stabilityOperator S m) := by
  intro u v huv
  have hzero : stabilityOperator S m (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  exact sub_eq_zero.mp (stability_kernel_trivial hS hz hm hsol hzero)

/-- Finite dimensionality upgrades injectivity to bijectivity. -/
theorem stability_bijective (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) :
    Function.Bijective (stabilityOperator S m) := by
  have hinj := stability_injective hS hz hm hsol
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The inverse stability operator, packaged as a linear equivalence. -/
def stabilityEquiv (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) :
    (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
  LinearEquiv.ofBijective (stabilityOperator S m) (stability_bijective hS hz hm hsol)

/-- Every inhomogeneous interior stability equation has exactly one solution. -/
theorem exists_unique_stability_solution (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (v : ι → ℂ) :
    ∃! u, stabilityOperator S m u = v := by
  obtain ⟨u, hu⟩ := (stability_bijective hS hz hm hsol).2 v
  exact ⟨u, hu, fun w hw => (stability_bijective hS hz hm hsol).1 (hw.trans hu.symm)⟩

/-- The stability inverse is continuous, since the coordinate space is finite
 dimensional. This is the Banach-space interface used by the inverse function theorem. -/
def stabilityContinuousEquiv (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) :
    (ι → ℂ) ≃L[ℂ] (ι → ℂ) :=
  (stabilityEquiv hS hz hm hsol).toContinuousLinearEquiv

/-- The inhomogeneous componentwise majorant for the stability equation. -/
theorem stability_norm_majorant (hS : ∀ i j, 0 ≤ S i j)
    (u : ι → ℂ) (i : ι) :
    ‖u i‖ ≤ ‖stabilityOperator S m u i‖ +
      ∑ j, (‖m i‖ ^ 2 * S i j) * ‖u j‖ := by
  have hui : u i = stabilityOperator S m u i +
      m i ^ 2 * ∑ j, (S i j : ℂ) * u j := by
    rw [stabilityOperator_apply]
    ring
  calc
    ‖u i‖ = ‖stabilityOperator S m u i +
        m i ^ 2 * ∑ j, (S i j : ℂ) * u j‖ := congrArg norm hui
    _ ≤ ‖stabilityOperator S m u i‖ +
        ‖m i ^ 2 * ∑ j, (S i j : ℂ) * u j‖ := norm_add_le _ _
    _ = ‖stabilityOperator S m u i‖ +
        ‖m i‖ ^ 2 * ‖∑ j, (S i j : ℂ) * u j‖ := by rw [norm_mul, norm_pow]
    _ ≤ ‖stabilityOperator S m u i‖ +
        ‖m i‖ ^ 2 * ∑ j, ‖(S i j : ℂ) * u j‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = ‖stabilityOperator S m u i‖ +
        ∑ j, (‖m i‖ ^ 2 * S i j) * ‖u j‖ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS i j)]
      ring

/-- An explicit interior inverse estimate in the natural imaginary-part weight.
If the forcing satisfies `|vᵢ| ≤ C η |mᵢ|²`, then the solution of `B u = v`
satisfies `|uᵢ| ≤ C Im mᵢ`. This derives the inverse bound from the actual
Dyson identity, without assuming a norm or spectral estimate. -/
theorem weighted_stability_estimate (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (u : ι → ℂ) (C : ℝ)
    (hforcing : ∀ i, ‖stabilityOperator S m u i‖ ≤ C * z.im * ‖m i‖ ^ 2) :
    ∀ i, ‖u i‖ ≤ C * (m i).im := by
  classical
  intro i
  haveI : Nonempty ι := ⟨i⟩
  obtain ⟨k, hk⟩ := Finite.exists_max (fun j => ‖u j‖ / (m j).im)
  let r : ℝ := ‖u k‖ / (m k).im
  have hpoint : ∀ j, ‖u j‖ ≤ r * (m j).im :=
    fun j => (div_le_iff₀ (hm j)).mp (hk j)
  have heq : ‖u k‖ = r * (m k).im :=
    (div_mul_cancel₀ _ (ne_of_gt (hm k))).symm
  have hbound : ‖u k‖ ≤ C * z.im * ‖m k‖ ^ 2 +
      r * ‖m k‖ ^ 2 * ∑ j, S k j * (m j).im := by
    calc
      ‖u k‖ ≤ ‖stabilityOperator S m u k‖ +
          ∑ j, (‖m k‖ ^ 2 * S k j) * ‖u j‖ := stability_norm_majorant hS u k
      _ ≤ C * z.im * ‖m k‖ ^ 2 +
          ∑ j, (‖m k‖ ^ 2 * S k j) * (r * (m j).im) := by
        exact add_le_add (hforcing k) (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hpoint j) (mul_nonneg (sq_nonneg _) (hS k j)))
      _ = C * z.im * ‖m k‖ ^ 2 +
          r * ‖m k‖ ^ 2 * ∑ j, S k j * (m j).im := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hid := BasicEstimates.weighted_imaginary_part_identity hm hsol k
  rw [Complex.normSq_eq_norm_sq] at hid
  have hnorm : 0 < ‖m k‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm k)) 2
  have hr : r ≤ C := by
    apply (mul_le_mul_iff_left₀ (mul_pos hz hnorm)).mp
    rw [heq, hid] at hbound
    nlinarith
  exact (hpoint i).trans (mul_le_mul_of_nonneg_right hr (le_of_lt (hm i)))

/-- Equivalent estimate for a solution of `B u = v`, with the forcing
normalized by the exact positive interior deficit `η |mᵢ|²`. -/
theorem weighted_stability_estimate_of_ratio_bound (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (u v : ι → ℂ) (C : ℝ) (huv : stabilityOperator S m u = v)
    (hforcing : ∀ i, ‖v i‖ / (z.im * ‖m i‖ ^ 2) ≤ C) :
    ∀ i, ‖u i‖ ≤ C * (m i).im := by
  apply weighted_stability_estimate hS hz hm hsol u C
  intro i
  rw [huv]
  have hpos : 0 < z.im * ‖m i‖ ^ 2 :=
    mul_pos hz (pow_pos (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm i)) 2)
  simpa only [mul_assoc] using (div_le_iff₀ hpos).mp (hforcing i)

/-- A componentwise bound on the actual inverse operator. -/
theorem weighted_inverse_estimate (hS : ∀ i j, 0 ≤ S i j)
    (hz : 0 < z.im) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (v : ι → ℂ) (C : ℝ)
    (hforcing : ∀ i, ‖v i‖ / (z.im * ‖m i‖ ^ 2) ≤ C) :
    ∀ i, ‖(stabilityEquiv hS hz hm hsol).symm v i‖ ≤ C * (m i).im := by
  apply weighted_stability_estimate_of_ratio_bound hS hz hm hsol
    ((stabilityEquiv hS hz hm hsol).symm v) v C _ hforcing
  exact (stabilityEquiv hS hz hm hsol).apply_symm_apply v

end NonSymmetricDyson.InteriorStability
