import Dyson.Full.Linear

/-! Operator-norm transfer to the unnormalized Euclidean space used in M6.
The conjugated operators are actual continuous linear maps, and all comparison
constants are explicit. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.EuclideanInverse

variable {ι : Type*} [Fintype ι]

def conjugate (f : (ι → ℂ) →L[ℂ] (ι → ℂ)) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.comp
    (f.comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).toContinuousLinearMap)

theorem conjugate_apply (f : (ι → ℂ) →L[ℂ] (ι → ℂ)) (u : ι → ℂ) :
    conjugate f (WithLp.toLp 2 u) = WithLp.toLp 2 (f u) := rfl

theorem conjugate_norm_upper (f : (ι → ℂ) →L[ℂ] (ι → ℂ)) :
    ‖conjugate f‖ ≤ Real.sqrt (Fintype.card ι) * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change Norms.euclideanNorm (f (WithLp.ofLp u)) ≤ _
  calc
    _ ≤ Real.sqrt (Fintype.card ι) * ‖f (WithLp.ofLp u)‖ :=
      Norms.euclidean_le_sqrt_card_mul_sup _
    _ ≤ Real.sqrt (Fintype.card ι) * (‖f‖ * ‖WithLp.ofLp u‖) :=
      mul_le_mul_of_nonneg_left (f.le_opNorm _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (Fintype.card ι) * (‖f‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Norms.sup_le_euclidean (WithLp.ofLp u)) (norm_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem conjugate_norm_lower (f : (ι → ℂ) →L[ℂ] (ι → ℂ)) :
    ‖f‖ ≤ Real.sqrt (Fintype.card ι) * ‖conjugate f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  calc
    ‖f u‖ ≤ Norms.euclideanNorm (f u) := Norms.sup_le_euclidean _
    _ = ‖conjugate f (WithLp.toLp 2 u)‖ := rfl
    _ ≤ ‖conjugate f‖ * Norms.euclideanNorm u := (conjugate f).le_opNorm _
    _ ≤ ‖conjugate f‖ * (Real.sqrt (Fintype.card ι) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (Norms.euclidean_le_sqrt_card_mul_sup u) (norm_nonneg _)
    _ = _ := by ring

def inverse (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ)) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  conjugate e.symm.toContinuousLinearMap

/-- A supremum lower bound produces the actual Euclidean inverse upper bound. -/
theorem inverse_upper_of_sup_lower (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ))
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ u, ‖u‖ ≤ C * ‖e u‖) :
    ‖inverse e‖ ≤ Real.sqrt (Fintype.card ι) * C := by
  have hs : ‖e.symm.toContinuousLinearMap‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    simpa using h (e.symm u)
  exact (conjugate_norm_upper _).trans
    (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _))

/-- An exact vector identity gives a lower bound without any spectral
normality assumption. This is the identity used in the bipartite origin case. -/
theorem inverse_identity_bound (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ))
    (v b : ι → ℂ) (ζ : ℂ) (he : e v = ζ • b) :
    Norms.euclideanNorm v ≤ ‖inverse e‖ * (‖ζ‖ * Norms.euclideanNorm b) := by
  have hi : e.symm (ζ • b) = v := by rw [← he, e.symm_apply_apply]
  have h := (inverse e).le_opNorm (WithLp.toLp 2 (ζ • b))
  change Norms.euclideanNorm (e.symm (ζ • b)) ≤
    ‖inverse e‖ * Norms.euclideanNorm (ζ • b) at h
  rw [hi] at h
  have hsmul : Norms.euclideanNorm (ζ • b) = ‖ζ‖ * Norms.euclideanNorm b := by
    change ‖ζ • WithLp.toLp 2 b‖ = _
    exact norm_smul ζ _
  simpa only [hsmul] using h

theorem inverse_lower_of_identity (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ))
    (v b : ι → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0)
    (hb : 0 < Norms.euclideanNorm b) (he : e v = ζ • b) :
    Norms.euclideanNorm v / (‖ζ‖ * Norms.euclideanNorm b) ≤ ‖inverse e‖ := by
  exact (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hζ) hb)).mpr
    (inverse_identity_bound e v b ζ he)

/-- Uniform lower estimate from quantitative numerator/denominator bounds. -/
theorem inverse_uniform_lower_of_identity (e : (ι → ℂ) ≃L[ℂ] (ι → ℂ))
    (v b : ι → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hv : a ≤ Norms.euclideanNorm v)
    (hb : Norms.euclideanNorm b ≤ B) (he : e v = ζ • b) :
    (a/B) / ‖ζ‖ ≤ ‖inverse e‖ := by
  have h := inverse_identity_bound e v b ζ he
  have hi : 0 ≤ ‖inverse e‖ := norm_nonneg _
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hb (norm_nonneg ζ)) hi
  apply (div_le_iff₀ (norm_pos_iff.mpr hζ)).mpr
  apply (div_le_iff₀ hB).mpr
  nlinarith

def stabilityInverse (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m) :=
  inverse (InteriorStability.stabilityContinuousEquiv hS hz hm heq)

theorem stability_inverse_upper (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ u, ‖u‖ ≤ C * ‖InteriorStability.stabilityOperator S m u‖) :
    ‖stabilityInverse S a z m hS hz hm heq‖ ≤ Real.sqrt (Fintype.card ι) * C :=
  inverse_upper_of_sup_lower _ C hC h

theorem stability_inverse_lower (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (v b : ι → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hv : A ≤ Norms.euclideanNorm v)
    (hb : Norms.euclideanNorm b ≤ B)
    (hid : InteriorStability.stabilityOperator S m v = ζ • b) :
    (A/B) / ‖ζ‖ ≤ ‖stabilityInverse S a z m hS hz hm heq‖ :=
  inverse_uniform_lower_of_identity _ v b ζ hζ A B hA hB hv hb hid

end NonSymmetricDyson.Full.EuclideanInverse
