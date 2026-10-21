import Dyson.Full.Singularities
import Dyson.Full.CubicPositivity
import Dyson.Full.Origin
import Dyson.Full.BulkGraph
import Dyson.Full.BulkDyson

/-! Original Jensen-equality route of the revised paper, lines 2690–3073.
This module never invokes the alternative Möbius-family nondegeneracy proof. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NonSymmetricDyson.Paper.SingularitiesJensen
open Full.Singularities
variable {ι : Type*} [Fintype ι]

/-- Equality in the stationary Jensen inequality gives the paper's exact
coboundary h_i=y_i-y_j along every positive matrix entry. -/
theorem zero_cubic_edge_difference
    (F : ι → ι → ℝ) (p l r u : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j)
    (hu : ∀ i, u i - ∑ j, F i j * u j = p i * r i ^ 2)
    (hψ : cubicCoefficient F p l r u = 0) :
    ∀ i j, 0 < F i j → u i / r i - u j / r j = p i * r i := by
  have he := cubicCoefficient_zero_edge F p l r u hF hl hr hFr hlF hu hψ
  intro i j hij
  rw [he i j hij, ← sub_div, hu]
  field_simp [(hr i).ne']

/-- In a symmetric support graph, a row-equality coboundary alternates
across every edge. This is the distance-two equality-space argument. -/
theorem symmetric_coboundary_alternates
    (E : ι → ι → Prop) (hsym : ∀ i j, E i j → E j i)
    (y h : ι → ℝ) (hc : ∀ i j, E i j → y i - y j = h i) :
    ∀ i j, E i j → h j = -h i := by
  intro i j hij
  linarith [hc i j hij, hc j i (hsym i j hij)]

/-- The original distance-two statement, before distinguishing the two
possible components of a connected symmetric support graph. -/
theorem coboundary_constant_on_row
    (E : ι → ι → Prop) (y h : ι → ℝ)
    (hc : ∀ i j, E i j → y i-y j=h i)
    (i j k : ι) (hij : E i j) (hik : E i k) : y j = y k := by
  linarith [hc i j hij, hc i k hik]

/-- A nonzero alternating signed positive vector has constant magnitude
along edges and opposite signs, precisely the paper's bipartite mode. -/
theorem signed_positive_alternation (p r : ι → ℝ)
    (hp : ∀ i, p i ^ 2 = 1) (hr : ∀ i, 0 < r i)
    (i j : ι) (h : p j * r j = -(p i * r i)) :
    r j = r i ∧ p j = -p i := by
  rcases sq_eq_one_iff.mp (hp i) with hi | hi
  · rcases sq_eq_one_iff.mp (hp j) with hj | hj
    · rw [hi, hj] at h
      exfalso
      nlinarith [hr i, hr j]
    · refine ⟨?_, by rw [hi, hj]⟩
      rw [hi, hj] at h
      linarith
  · rcases sq_eq_one_iff.mp (hp j) with hj | hj
    · refine ⟨?_, by rw [hi, hj]; ring⟩
      rw [hi, hj] at h
      linarith
    · rw [hi, hj] at h
      exfalso
      nlinarith [hr i, hr j]

/-- Perron plus Dyson excludes the only alternating equality mode unless
the potential is identically the boundary energy. This uses exactly the
paper's substitution, without a rational solution family. -/
theorem alternating_perron_forces_constant_potential
    (S : ι → ι → ℝ) (a m p q r : ι → ℝ) (τ : ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (hp : ∀ i, p i ^ 2 = 1)
    (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i)
    (hm : ∀ i, m i = p i*q i)
    (hFr : ∀ i, ∑ j, (q i*S i j*q j)*r j=r i)
    (hsol : ∀ i, -(m i)⁻¹=τ-a i+∑ j, S i j*m j)
    (halt : ∀ i j, 0<S i j → p j*r j=-(p i*r i)) :
    ∀ i, a i=τ := by
  have hn (i : ι) : p i ≠ 0 := by
    intro hz
    have hh := hp i
    simp [hz] at hh
  have hmn (i : ι) : m i ≠ 0 := by rw [hm]; exact mul_ne_zero (hn i) (hq i).ne'
  intro i
  have hedges (j : ι) (hs : 0<S i j) := signed_positive_alternation p r hp hr i j (halt i j hs)
  have hrow : q i*(∑ j,S i j*q j)=1 := by
    have hf := hFr i
    have he : (∑ j,(q i*S i j*q j)*r j) =
        (q i*(∑ j,S i j*q j))*r i := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hs : 0<S i j
      · rw [(hedges j hs).1]; ring
      · have hz : S i j=0 := le_antisymm (le_of_not_gt hs) (hS i j)
        simp [hz]
    rw [he] at hf
    nlinarith [hr i]
  have hsum : (∑ j,S i j*m j) = -p i*(∑ j,S i j*q j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : 0<S i j
    · rw [hm, (hedges j hs).2]; ring
    · have hz : S i j=0 := le_antisymm (le_of_not_gt hs) (hS i j)
      simp [hz]
  have he := hsol i
  rw [hsum, hm] at he
  have hmul := congrArg (fun x : ℝ => (p i*q i)*x) he
  have hinv : (p i*q i)*(p i*q i)⁻¹=1 := mul_inv_cancel₀ (mul_ne_zero (hn i) (hq i).ne')
  have hpterm : p i^2*(q i*(∑ j,S i j*q j))=1 := by rw [hp,hrow]; norm_num
  have hh : (p i*q i)*(τ-a i)=0 := by nlinarith [hpterm]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero (hn i) (hq i).ne'))).symm

end NonSymmetricDyson.Paper.SingularitiesJensen
