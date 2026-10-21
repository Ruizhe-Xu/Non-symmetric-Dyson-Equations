import Dyson.Full.SingularSpectralAlgebra
import Dyson.Full.PhaseTaylor

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def normalizedImag (m : ι → ℂ) (i : ι) : ℝ := (m i).im/‖m i‖
def perronDensity (l : ι → ℝ) (m : ι → ℂ) : ℝ := ∑ i, l i*normalizedImag m i
def phaseOperator (m : ι → ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  diagonal (fun i => star (m i)/m i)
def saturatedOperator (S : Matrix ι ι ℝ) (m : ι → ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  complexMatrixOperator (fun i j => ‖m i‖*S i j*‖m j‖)

theorem diagonal_norm_le (d : ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ i, ‖d i‖ ≤ B) : ‖diagonal d‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg _))).mpr
  intro i
  change ‖d i*x i‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hd i) (norm_le_pi_norm x i) (norm_nonneg _) hB

theorem phase_distance_one (m : ℂ) (hm : m ≠ 0) :
    ‖star m/m-1‖ = 2*|m.im/‖m‖| := by
  have he : star m/m-1 = (-2*Complex.I*(m.im:ℂ))/m := by
    field_simp
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [he, norm_div, norm_mul, norm_mul]
  simp only [norm_neg, PhaseTaylor.complex_norm_two, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_norm, mul_one]
  ring

theorem phase_operator_bound (m : ι → ℂ) (hm : ∀ i, m i ≠ 0)
    (δ V : ℝ) (hδ : 0 ≤ δ) (hV : 0 ≤ V)
    (hv : ∀ i, |normalizedImag m i| ≤ V*δ) :
    ‖phaseOperator m-ContinuousLinearMap.id ℂ (ι → ℂ)‖ ≤ 2*V*δ := by
  have he : phaseOperator m-ContinuousLinearMap.id ℂ (ι → ℂ) =
      diagonal (fun i => star (m i)/m i-1) := by
    ext x i
    simp [phaseOperator, diagonal_apply]
    ring
  rw [he]
  apply diagonal_norm_le _ _ (by positivity)
  intro i
  rw [phase_distance_one _ (hm i)]
  exact (mul_le_mul_of_nonneg_left (hv i) (by norm_num)).trans_eq (by ring)

theorem phase_operator_taylor (m : ι → ℂ) (hm : ∀ i, m i ≠ 0)
    (p r t : ι → ℝ) (δ η R T : ℝ)
    (hp : ∀ i, p i^2=1) (hsign : ∀ i, 0 ≤ p i*(m i).re)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hr : ∀ i, |r i| ≤ R) (ht : ∀ i, |t i| ≤ T)
    (hv : ∀ i, normalizedImag m i=δ*r i+η*t i) :
    ‖phaseOperator m-ContinuousLinearMap.id ℂ (ι → ℂ) -
        (δ:ℂ) • firstPhase p r - ((δ:ℂ)^2) • secondPhase r‖ ≤
      (1+8*(R^3+T^3)+2*T*(2+R))*(δ^3+η) := by
  have he : phaseOperator m-ContinuousLinearMap.id ℂ (ι → ℂ) -
        (δ:ℂ) • firstPhase p r - ((δ:ℂ)^2) • secondPhase r =
      diagonal (fun i => star (m i)/m i-PhaseTaylor.phasePolynomial (p i) (δ*r i)) := by
    ext x i
    simp [phaseOperator, firstPhase, secondPhase, PhaseTaylor.phasePolynomial, diagonal_apply]
    ring
  rw [he]
  apply diagonal_norm_le _ _ (by positivity)
  intro i
  exact PhaseTaylor.phase_substitution_error _ (hm i) _ _ _ _ _ _ _ (hp i) (hsign i)
    hδ hδ1 hη hη1 hR hT (hr i) (ht i) (hv i)

theorem perron_density_nonneg (l : ι → ℝ) (m : ι → ℂ)
    (hl : ∀ i, 0 ≤ l i) (hv : ∀ i, 0 ≤ normalizedImag m i) :
    0 ≤ perronDensity l m := Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (hv i))

theorem normalizedImag_le_density (l : ι → ℝ) (m : ι → ℂ) (b : ℝ)
    (hb : 0 < b) (hl : ∀ i, b ≤ l i) (hv : ∀ i, 0 ≤ normalizedImag m i) (i : ι) :
    |normalizedImag m i| ≤ b⁻¹*perronDensity l m := by
  rw [abs_of_nonneg (hv i), inv_mul_eq_div]
  apply (le_div_iff₀ hb).mpr
  calc
    normalizedImag m i*b ≤ l i*normalizedImag m i := by nlinarith [mul_le_mul_of_nonneg_right (hl i) (hv i)]
    _ ≤ perronDensity l m := Finset.single_le_sum
      (fun j _ => mul_nonneg (hb.le.trans (hl j)) (hv j)) (Finset.mem_univ i)

theorem perron_density_identity
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (l : ι → ℝ) (lam : ℝ)
    (hleft : ∀ j, ∑ i, l i*(‖m i‖*S i j*‖m j‖)=lam*l j) :
    (1-lam)*perronDensity l m = z.im*(∑ i, l i*‖m i‖) := by
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => congrArg (fun v : ℝ => l i*v)
      (normalized_imaginary_identity S a z m hm hsol i))
  have hsum : (∑ i, l i*∑ j, (‖m i‖*S i j*‖m j‖)*normalizedImag m j) =
      lam*perronDensity l m := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [perronDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ i, l i*((‖m i‖*S i j*‖m j‖)*normalizedImag m j)) =
          (∑ i, l i*(‖m i‖*S i j*‖m j‖))*normalizedImag m j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = lam*(l j*normalizedImag m j) := by rw [hleft]; ring
  change (∑ i, l i*(normalizedImag m i - ∑ j,
    (‖m i‖*S i j*‖m j‖)*normalizedImag m j)) = ∑ i, l i*(z.im*‖m i‖) at hh
  simp only [mul_sub, Finset.sum_sub_distrib] at hh
  rw [hsum] at hh
  have hr : (∑ i, l i*(z.im*‖m i‖)) = z.im*∑ i, l i*‖m i‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hr] at hh
  dsimp [perronDensity] at hh ⊢
  linarith

theorem firstPhase_norm_le (p r : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hp : ∀ i, p i^2=1) (hr : ∀ i, |r i| ≤ R) : ‖firstPhase p r‖ ≤ 2*R := by
  rw [firstPhase, norm_smul]
  have hc : ‖(-2*Complex.I:ℂ)‖=2 := by simp [PhaseTaylor.complex_norm_two]
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply diagonal_norm_le _ _ hR
  intro i
  have hpabs : |p i|=1 := by nlinarith [sq_abs (p i), abs_nonneg (p i), hp i]
  simpa [norm_mul, hpabs] using hr i

theorem secondPhase_norm_le (r : ι → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, |r i| ≤ R) : ‖secondPhase r‖ ≤ 2*R^2 := by
  rw [secondPhase, norm_smul]
  have hc : ‖(-2:ℂ)‖=2 := by simp [PhaseTaylor.complex_norm_two]
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply diagonal_norm_le _ _ (sq_nonneg _)
  intro i
  simpa [norm_pow] using pow_le_pow_left₀ (abs_nonneg (r i)) (hr i) 2

theorem imaginary_direction_real
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (r l t : ι → ℝ) (K : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hK : IsRestrictedInverse (saturatedOperator S m).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ)))
    (hKt : K (fun i => (‖m i‖:ℂ)) = fun i => (t i:ℂ)) :
    ∀ i, normalizedImag m i=perronDensity l m*r i+z.im*t i := by
  have hh := imaginary_direction S a z m hm hsol (saturatedOperator S m) K
    (complexFunctional l) (fun i => (r i:ℂ)) (fun _ _ => rfl) hK
  dsimp only at hh
  rw [hKt] at hh
  have he : complexFunctional l (fun i => ((m i).im/‖m i‖:ℝ)) =
      (perronDensity l m:ℂ) := by
    simp [complexFunctional_apply, perronDensity, normalizedImag]
  rw [he] at hh
  intro i
  have hi := congrFun hh i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  exact_mod_cast hi

theorem perron_scaled_height
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (l : ι → ℝ) (lam : ℝ) (hη : 0 ≤ z.im)
    (hl : ∀ i, 0 ≤ l i) (hv : ∀ i, 0 ≤ normalizedImag m i)
    (hleft : ∀ j, ∑ i, l i*(‖m i‖*S i j*‖m j‖)=lam*l j) :
    |1-lam| * perronDensity l m = z.im*(∑ i, l i*‖m i‖) := by
  have hδ := perron_density_nonneg l m hl hv
  have hμ : 0 ≤ ∑ i, l i*‖m i‖ := Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (norm_nonneg _))
  calc
    |1-lam| * perronDensity l m = |(1-lam)*perronDensity l m| := by rw [abs_mul, abs_of_nonneg hδ]
    _ = |z.im*(∑ i, l i*‖m i‖)| := congrArg abs (perron_density_identity S a z m hm hsol l lam hleft)
    _ = z.im*(∑ i, l i*‖m i‖) := abs_of_nonneg (mul_nonneg hη hμ)

end NonSymmetricDyson.Full.SingularSpectral
