import Dyson.Paper.PerronTransport

/-! Original Proposition I-F-second, connected to the original Markov proof
through the actual Perron diagonal conjugation. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.Perron
open Full Full.Singularities
theorem original_uniform_saturated_restricted_inverse_bound
    (frobenius : ClassicalFrobenius.ExternalCitedFrobeniusTheory) {n : ℕ} (hn : 0 < n)
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
  obtain ⟨D,N,hD,hN,hmarkov⟩ := original_markov_projected_inverse frobenius hn S hS hirr
  let kappa : ℝ := min 1 (c ^ 2 * s * cr / U)
  have hk0 : 0 < kappa := lt_min (by norm_num) (by positivity)
  have hk1 : kappa ≤ 1 := min_le_left _ _
  let B := Real.sqrt n * (1 * (Real.sqrt n *
    (D / kappa ^ N)) * cr⁻¹)
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
  let Q := BulkAlgebra.normalizedMarkov (saturatedMatrix S m) r lam
  let pi : Fin n → ℝ := fun i => l i*r i
  have hQ : ∀ i j,0≤Q i j := BulkAlgebra.normalizedMarkov_nonnegative _ r lam hF hr hlamp
  have hrow : ∀ i,∑ j,Q i j=1 := BulkAlgebra.normalizedMarkov_row_sum _ r lam hr hlamp hright
  have hmpos (i : Fin n) : 0<‖m i‖ := by
    have hh : 0<scale*‖m i‖ := hc.trans_le (hlo i)
    exact (mul_pos_iff_of_pos_left hscale).mp hh
  have hsupp : ∀ i j,0<Q i j ↔ 0<S i j := by
    intro i j
    constructor
    · intro hh
      by_contra hz
      have hz0 : S i j=0 := le_antisymm (le_of_not_gt hz) (hS i j)
      simp [Q,BulkAlgebra.normalizedMarkov,saturatedMatrix,hz0] at hh
    · intro hij
      exact div_pos (mul_pos (mul_pos (mul_pos (hmpos i) hij) (hmpos j)) (hr j))
        (mul_pos hlamp (hr i))
  have hpistat : ∀ j,∑ i,pi i*Q i j=pi j := by
    intro j
    have he (i : Fin n) : pi i*Q i j=(l i*saturatedMatrix S m i j)*(r j/lam) := by
      dsimp [pi,Q,BulkAlgebra.normalizedMarkov]
      field_simp [(hr i).ne',hlamp.ne']
    simp_rw [he]
    rw [← Finset.sum_mul,hleft]
    dsimp [pi]
    field_simp
  obtain ⟨J,hJ,hJn⟩ := hmarkov Q hQ hrow hsupp pi (fun i => mul_nonneg (hl i).le (hr i).le)
    hpair hpistat kappa hk0 hk1 hsupportQ lam hlamp.le hlam1
  obtain ⟨K,hK⟩ := perron_inverse_transport (saturatedMatrix S m) r l lam hr hlamp
    cr 1 (D/kappa^N) hcr (by norm_num) (by positivity)
    (fun i => (hR i).1) (fun i => (hR i).2) J hJ hJn
  refine ⟨K,hK.1,hK.2.1,hK.2.2.1,hK.2.2.2.1,?_⟩
  simpa only [Fintype.card_fin] using hK.2.2.2.2

end NonSymmetricDyson.Paper.Perron
