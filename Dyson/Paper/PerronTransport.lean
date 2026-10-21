import Dyson.Paper.PerronMarkov
import Dyson.Full.PerronRestricted

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.Perron
open Full Full.Singularities
variable {V : Type*} [Fintype V] [Nonempty V]

/-- Original diagonal conjugation, accepting the inverse just constructed
by the Fourier–Doeblin proof. -/
theorem perron_inverse_transport
    (F : Matrix V V ℝ) (r l : V → ℝ) (lam : ℝ)
    (hr : ∀ i,0<r i) (hlamp : 0<lam)
    (b B D : ℝ) (hb : 0<b) (hB : 0<B) (hD : 0≤D)
    (hrlo : ∀ i,b≤r i) (hrhi : ∀ i,r i≤B)
    (J : (V → ℂ) →L[ℂ] (V → ℂ))
    (hJ : BulkMarkovComplete.IsProjectedInverse (BulkAlgebra.normalizedMarkov F r lam)
      (fun i => l i*r i) lam J)
    (hJnorm : ‖EuclideanInverse.conjugate J‖≤D) :
    ∃ K : (V → ℂ) →L[ℂ] (V → ℂ),
      K (fun i => (r i:ℂ))=0 ∧ (∀ x,complexFunctional l (K x)=0) ∧
      (∀ x,K x-complexMatrixOperator F (K x)=x-complexFunctional l x • (fun i => (r i:ℂ))) ∧
      (∀ x,K (x-complexMatrixOperator F x)=x-complexFunctional l x • (fun i => (r i:ℂ))) ∧
      ‖EuclideanInverse.conjugate K‖≤Real.sqrt (Fintype.card V)*(B*(Real.sqrt (Fintype.card V)*D)*b⁻¹) := by
  let Q := BulkAlgebra.normalizedMarkov F r lam
  let pi : V → ℝ := fun i => l i*r i
  obtain ⟨hJone,hJleft,hJrightinv,hJleftinv⟩ := hJ
  let R : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
    { toFun := fun x i => (r i : ℂ) * x i
      map_add' := by intro x y; ext i; simp [mul_add]
      map_smul' := by intro c x; ext i; simp [mul_left_comm] }
  let Ri : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
    { toFun := fun x i => x i / (r i : ℂ)
      map_add' := by intro x y; ext i; simp [add_div]
      map_smul' := by intro c x; ext i; simp [mul_div_assoc] }
  let K := R.toContinuousLinearMap.comp (J.comp Ri.toContinuousLinearMap)
  have hrc (i : V) : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
  have hR (x : V → ℂ) : R x = fun i => (r i : ℂ) * x i := rfl
  have hRi (x : V → ℂ) : Ri x = fun i => x i / (r i : ℂ) := rfl
  have hK (x : V → ℂ) : K x = R (J (Ri x)) := rfl
  have hRRi (x : V → ℂ) : R (Ri x) = x := by
    ext i
    simp only [hR, hRi]
    field_simp [hrc i]
  have hRiR (x : V → ℂ) : Ri (R x) = x := by ext i; simp [hR, hRi, hrc]
  have hmean (x : V → ℂ) : ∑ i, (pi i : ℂ) * Ri x i = complexFunctional l x := by
    rw [complexFunctional_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pi, Complex.ofReal_mul, hRi]
    field_simp [hrc i]
  have hconj (x : V → ℂ) : R (MarkovStability.phaseMarkovOperator Q (fun _ => 1) lam (Ri x)) =
      x - complexMatrixOperator F x := by
    ext i
    have hh := BulkAlgebra.normalizedMarkov_conjugation F r lam (fun i => (hr i).ne') hlamp.ne' (fun _ => 1) x i
    simpa only [hR, hRi, Q, one_mul, Pi.sub_apply, Model.action_apply, complexMatrixOperator_apply] using hh
  have hconji (x : V → ℂ) : Ri (x - complexMatrixOperator F x) =
      MarkovStability.phaseMarkovOperator Q (fun _ => 1) lam (Ri x) := by
    rw [← hconj, hRiR]
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · have hi : Ri (fun i => (r i : ℂ)) = fun _ => 1 := by ext i; simp [hRi, hrc]
    rw [hK, hi, hJone, map_zero]
  · intro x
    rw [hK, complexFunctional_apply]
    convert hJleft (Ri x) using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [hR, pi, mul_assoc]
  · intro x
    rw [← hconj, hK, hRiR, hJrightinv, map_sub, map_smul, hRRi, hmean]
    simp [hR]
  · intro x
    rw [hK, hconji, hJleftinv, map_sub, map_smul, hRRi, hmean]
    simp [hR]
  · have hRiBound (x : V → ℂ) : ‖Ri x‖ ≤ b⁻¹ * ‖x‖ := by
      have he : Ri x = fun i => (r i : ℂ)⁻¹ * x i := by ext i; simp [hRi, div_eq_mul_inv, mul_comm]
      rw [he]
      apply BulkAlgebra.diagonal_upper _ _ b⁻¹ (by positivity)
      intro i
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr i)]
      exact inv_anti₀ hb (hrlo i)
    have hRBound (x : V → ℂ) : ‖R x‖ ≤ B * ‖x‖ := by
      rw [hR]
      apply BulkAlgebra.diagonal_upper _ _ B hB.le
      intro i
      simpa [Complex.norm_real, abs_of_pos (hr i)] using hrhi i
    have hJn := (EuclideanInverse.conjugate_norm_lower J).trans
      (mul_le_mul_of_nonneg_left hJnorm (Real.sqrt_nonneg _))
    have hKn : ‖K‖ ≤ B * (Real.sqrt (Fintype.card V) *
        D) * b⁻¹ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro x
      rw [hK]
      calc
        _ ≤ B * ‖J (Ri x)‖ := hRBound _
        _ ≤ B * (‖J‖ * ‖Ri x‖) := mul_le_mul_of_nonneg_left (J.le_opNorm _) hB.le
        _ ≤ B * ((Real.sqrt (Fintype.card V) *
            D) * (b⁻¹ * ‖x‖)) := by
          gcongr
          exact hRiBound x
        _ = _ := by ring
    exact (EuclideanInverse.conjugate_norm_upper K).trans
      (mul_le_mul_of_nonneg_left hKn (Real.sqrt_nonneg _))

end NonSymmetricDyson.Paper.Perron
