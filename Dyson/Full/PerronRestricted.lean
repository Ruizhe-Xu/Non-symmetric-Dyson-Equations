import Dyson.Full.PerronBounds
import Dyson.Full.BulkRestricted
import Dyson.Full.BulkAlgebra
import Dyson.Full.BulkKernel

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Singularities
variable {V : Type*} [Fintype V] [Nonempty V]

/-- The actual Perron conjugation transfers the quantitative Markov
restricted inverse to I-F, retaining both projection identities and an
explicit ordinary Euclidean operator bound. -/
theorem perron_restricted_inverse_bound
    (F : Matrix V V ℝ) (r l : V → ℝ) (lam : ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hr : ∀ i, 0 < r i) (hl : ∀ i, 0 ≤ l i)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hFr : ∀ i, ∑ j, F i j * r j = lam * r i)
    (hlF : ∀ j, ∑ i, l i * F i j = lam * l j)
    (hnorm : ∑ i, l i * r i = 1)
    (E : V → V → Prop) (hc : Resonance.StronglyConnected E)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hs : ∀ i j, E i j → kappa ≤ BulkAlgebra.normalizedMarkov F r lam i j)
    (b B : ℝ) (hb : 0 < b) (hB : 0 < B)
    (hrlo : ∀ i, b ≤ r i) (hrhi : ∀ i, r i ≤ B) :
    ∃ K : (V → ℂ) →L[ℂ] (V → ℂ),
      K (fun i => (r i : ℂ)) = 0 ∧
      (∀ x, complexFunctional l (K x) = 0) ∧
      (∀ x, K x - complexMatrixOperator F (K x) = x - complexFunctional l x • (fun i => (r i : ℂ))) ∧
      (∀ x, K (x - complexMatrixOperator F x) = x - complexFunctional l x • (fun i => (r i : ℂ))) ∧
      ‖EuclideanInverse.conjugate K‖ ≤
        Real.sqrt (Fintype.card V) * (B *
          (Real.sqrt (Fintype.card V) *
            (Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V))) * b⁻¹) := by
  let Q := BulkAlgebra.normalizedMarkov F r lam
  let pi : V → ℝ := fun i => l i * r i
  have hpi : ∀ i, 0 ≤ pi i := fun i => mul_nonneg (hl i) (hr i).le
  have hstationary : ∀ j, ∑ i, pi i * Q i j = pi j := by
    intro j
    have he (i : V) : pi i * Q i j = (l i * F i j) * (r j / lam) := by
      dsimp [pi, Q, BulkAlgebra.normalizedMarkov]
      field_simp [(hr i).ne', hlam.ne']
    simp_rw [he]
    rw [← Finset.sum_mul, hlF]
    dsimp [pi]
    field_simp
  obtain ⟨J, hJone, hJleft, hJrightinv, hJleftinv, hJnorm⟩ :=
    BulkRestricted.projected_inverse_bound E hc Q
      (BulkAlgebra.normalizedMarkov_nonnegative F r lam hF hr hlam)
      (BulkAlgebra.normalizedMarkov_row_sum F r lam hr hlam hFr)
      kappa hk0 hk1 hs pi hpi hnorm hstationary lam hlam.le hlam1
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
    have hh := BulkAlgebra.normalizedMarkov_conjugation F r lam (fun i => (hr i).ne') hlam.ne' (fun _ => 1) x i
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
        (Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V))) * b⁻¹ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro x
      rw [hK]
      calc
        _ ≤ B * ‖J (Ri x)‖ := hRBound _
        _ ≤ B * (‖J‖ * ‖Ri x‖) := mul_le_mul_of_nonneg_left (J.le_opNorm _) hB.le
        _ ≤ B * ((Real.sqrt (Fintype.card V) *
            (Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V))) * (b⁻¹ * ‖x‖)) := by
          gcongr
          exact hRiBound x
        _ = _ := by ring
    exact (EuclideanInverse.conjugate_norm_upper K).trans
      (mul_le_mul_of_nonneg_left hKn (Real.sqrt_nonneg _))

/-- The restricted inverse bound is uniform for the actual saturated matrix
on any region with the manuscript's scaled component bounds. All Markov
support constants and diagonal condition bounds are constructed from S,c,C. -/
theorem uniform_saturated_restricted_inverse_bound {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ B > 0, ∀ (scale : ℝ) (m : Fin n → ℂ) (r l : Fin n → ℝ) (lam : ℝ),
      0 < scale → (∀ i, c ≤ scale * ‖m i‖) → (∀ i, scale * ‖m i‖ ≤ C) →
      (∀ i, 0 < r i) → (∀ i, 0 < l i) →
      (∀ i, ∑ j, saturatedMatrix S m i j * r j = lam * r i) →
      (∀ j, ∑ i, l i * saturatedMatrix S m i j = lam * l j) →
      (∑ i, r i ^ 2 = 1) → (∑ i, l i * r i = 1) → lam ≤ 1 →
      ∃ K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
        K (fun i => (r i : ℂ)) = 0 ∧ (∀ x, complexFunctional l (K x) = 0) ∧
        (∀ x, K x - complexMatrixOperator (saturatedMatrix S m) (K x) =
          x - complexFunctional l x • (fun i => (r i : ℂ))) ∧
        (∀ x, K (x - complexMatrixOperator (saturatedMatrix S m) x) =
          x - complexFunctional l x • (fun i => (r i : ℂ))) ∧
        ‖EuclideanInverse.conjugate K‖ ≤ B := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨cr, hcr, cl, hcl, L, hL, U, hU, hall⟩ := uniform_saturated_perron_bounds hn S hS hirr c C hc hC
  obtain ⟨s, hs, _, hsupport⟩ := BulkKernel.exists_positive_support_bound S
  let kappa : ℝ := min 1 (c ^ 2 * s * cr / U)
  have hk0 : 0 < kappa := lt_min (by norm_num) (by positivity)
  have hk1 : kappa ≤ 1 := min_le_left _ _
  let B := Real.sqrt n * (1 * (Real.sqrt n *
    (Real.sqrt n * (8 * (n : ℝ)) / kappa ^ (2 * n))) * cr⁻¹)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro scale m r l lam hscale hlo hhi hr hl hright hleft hnorm hpair hlam1
  obtain ⟨hR, _, hlamlo, hlamhi⟩ := hall scale m r l lam hscale hlo hhi hr hl hright hleft hnorm hpair
  have hlamp : 0 < lam := (div_pos hL (sq_pos_of_pos hscale)).trans_le hlamlo
  have hF : ∀ i j, 0 ≤ saturatedMatrix S m i j :=
    fun i j => mul_nonneg (mul_nonneg (norm_nonneg _) (hS i j)) (norm_nonneg _)
  have hsupportQ : ∀ i j, 0 < S i j → kappa ≤
      BulkAlgebra.normalizedMarkov (saturatedMatrix S m) r lam i j := by
    intro i j hij
    apply (le_div_iff₀ (mul_pos hlamp (hr i))).mpr
    have hnum : c ^ 2 * s * cr ≤ scale ^ 2 * (saturatedMatrix S m i j * r j) := by
      calc
        c ^ 2 * s * cr = c * s * c * cr := by ring
        _ ≤ (scale * ‖m i‖) * S i j * (scale * ‖m j‖) * r j := by
          gcongr
          · exact hlo i
          · exact hsupport i j hij
          · exact hlo j
          · exact (hR j).1
        _ = _ := by dsimp [saturatedMatrix]; ring
    have hlamsq : scale ^ 2 * lam ≤ U := by
      simpa [mul_comm] using (le_div_iff₀ (sq_pos_of_pos hscale)).mp hlamhi
    have hden : scale ^ 2 * (lam * r i) ≤ U := by
      have hh := mul_le_of_le_one_right (mul_nonneg (sq_nonneg scale) hlamp.le) (hR i).2
      nlinarith
    have hkU : kappa * U ≤ c ^ 2 * s * cr :=
      (le_div_iff₀ hU).mp (min_le_right _ _)
    have hh := (mul_le_mul_of_nonneg_left hden hk0.le).trans (hkU.trans hnum)
    apply (mul_le_mul_left (sq_pos_of_pos hscale)).mp
    nlinarith
  obtain ⟨K, hK⟩ := perron_restricted_inverse_bound (saturatedMatrix S m) r l lam
    hF hr (fun i => (hl i).le) hlamp hlam1 hright hleft hpair
    (fun i j => 0 < S i j)
    (Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr)
    kappa hk0 hk1 hsupportQ cr 1 hcr (by norm_num)
    (fun i => (hR i).1) (fun i => (hR i).2)
  refine ⟨K, hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.1, ?_⟩
  simpa only [Fintype.card_fin] using hK.2.2.2.2

end NonSymmetricDyson.Full.Singularities
