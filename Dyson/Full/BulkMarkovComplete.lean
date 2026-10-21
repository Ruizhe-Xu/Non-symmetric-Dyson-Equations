import Dyson.Full.BulkRestricted

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkMarkovComplete
universe u
open Resonance MarkovStability
variable {V : Type u} [Fintype V] [Nonempty V]

/-- The actual minimum positive stochastic entry, including attainment. -/
theorem positive_minimum (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa ≤ 1 ∧
      (∃ i j, Q i j = kappa) ∧ (∀ i j, 0 < Q i j → kappa ≤ Q i j) := by
  let entries : Finset ℝ := (Finset.univ.filter fun p : V × V => 0 < Q p.1 p.2).image
    (fun p => Q p.1 p.2)
  have hex : ∃ i j, 0 < Q i j := by
    let i : V := Classical.arbitrary V
    by_contra hh
    push_neg at hh
    have hz : ∑ j, Q i j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (hh i j) (hQ i j)
    linarith [hrow i]
  have hne : entries.Nonempty := by
    obtain ⟨i,j,hij⟩ := hex
    exact ⟨Q i j,Finset.mem_image.mpr ⟨(i,j),by simp [hij],rfl⟩⟩
  let kappa := entries.min' hne
  have hmem : kappa ∈ entries := Finset.min'_mem entries hne
  obtain ⟨p,hp,hkp⟩ := Finset.mem_image.mp hmem
  have hp0 : 0 < Q p.1 p.2 := (Finset.mem_filter.mp hp).2
  have hk0 : 0 < kappa := by rwa [hkp] at hp0
  have hk1 : kappa ≤ 1 := by
    rw [← hkp,← hrow p.1]
    exact Finset.single_le_sum (fun j _ => hQ p.1 j) (Finset.mem_univ p.2)
  refine ⟨kappa,hk0,hk1,⟨p.1,p.2,hkp⟩,?_⟩
  intro i j hij
  exact Finset.min'_le entries (Q i j) (Finset.mem_image.mpr ⟨(i,j),by simp [hij],rfl⟩)

/-- Ordinary PF supplies a stationary vector; normalization is proved here. -/
theorem stationary_probability (external : BulkPerron.PerronLeftAndSimple.{u})
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hc : StronglyConnected (fun i j => 0 < Q i j)) :
    ∃ pi : V → ℝ, (∀ i, 0 < pi i) ∧ (∑ i, pi i = 1) ∧
      (∀ j, ∑ i, pi i * Q i j = pi j) := by
  obtain ⟨l,hl,hleft,_⟩ := external Q hQ hc (fun _ => 1) (by simp)
    (fun i => by simpa using hrow i)
  have ht : 0 < ∑ i, l i := Finset.sum_pos (fun i _ => hl i) Finset.univ_nonempty
  refine ⟨fun i => l i / ∑ j, l j,fun i => div_pos (hl i) ht,?_,?_⟩
  · rw [← Finset.sum_div,div_self ht.ne']
  · intro j
    simp_rw [div_mul_eq_mul_div,← Finset.sum_div,hleft]

def IsProjectedInverse (Q : Matrix V V ℝ) (pi : V → ℝ) (lam : ℝ)
    (K : (V → ℂ) →L[ℂ] (V → ℂ)) : Prop :=
  K (fun _ : V => (1 : ℂ)) = 0 ∧
  (∀ x, (∑ i, (pi i : ℂ) * K x i) = 0) ∧
  (∀ x, phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam (K x) =
    x - (∑ i, (pi i : ℂ) * x i) • (fun _ : V => (1 : ℂ))) ∧
  (∀ x, K (phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam x) =
    x - (∑ i, (pi i : ℂ) * x i) • (fun _ : V => (1 : ℂ)))

theorem stationary_unique (Q : Matrix V V ℝ) (pi : V → ℝ)
    (K : (V → ℂ) →L[ℂ] (V → ℂ)) (hK : IsProjectedInverse Q pi 1 K)
    (mu : V → ℝ) (hmusum : ∑ i, mu i = 1)
    (hmu : ∀ j, ∑ i, mu i * Q i j = mu j) : mu = pi := by
  let ell := BulkPerron.pairing (fun i => (mu i : ℂ))
  have hQell (x : V → ℂ) : ell (Model.action Q x) = ell x := by
    change BulkPerron.pairing _ _ = _
    rw [BulkPerron.pairing_action]
    have he : Model.action Q.transpose (fun i => (mu i : ℂ)) = fun i => (mu i : ℂ) := by
      ext j
      have hh := congrArg (fun r : ℝ => (r : ℂ)) (hmu j)
      simpa [Model.action_apply,mul_comm] using hh
    rw [he]
  have hunit : ell (fun _ : V => (1 : ℂ)) = 1 := by
    change (∑ i, (mu i : ℂ) * 1) = 1
    simp only [mul_one,← Complex.ofReal_sum,hmusum,Complex.ofReal_one]
  have hmean (x : V → ℂ) : ell x = ∑ i, (pi i : ℂ) * x i := by
    have hh := congrArg ell (hK.2.2.1 x)
    have hp : phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) 1 (K x) = K x - Model.action Q (K x) := by
      ext i
      simp [phaseMarkovOperator_apply,Model.action_apply]
    rw [hp,map_sub,hQell,sub_self,map_sub,map_smul,hunit,smul_eq_mul,mul_one] at hh
    exact (sub_eq_zero.mp hh.symm)
  ext j
  have hh := hmean (Pi.single j (1 : ℂ))
  have hc : (mu j : ℂ) = (pi j : ℂ) := by
    simpa [ell,BulkPerron.pairing,Pi.single_apply,mul_ite] using hh
  exact Complex.ofReal_injective hc

/-- The original Markov restricted-inverse lemma, with the invariant
probability vector, its uniqueness and the actual minimum entry constructed.
The support exponent is the explicit positive integer 2*card(V). -/
theorem markov_restricted_inverse (external : BulkPerron.PerronLeftAndSimple.{u})
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hc : StronglyConnected (fun i j => 0 < Q i j)) :
    ∃ (pi : V → ℝ) (kappa : ℝ),
      (∀ i, 0 < pi i) ∧ (∑ i, pi i = 1) ∧
      (∀ j, ∑ i, pi i * Q i j = pi j) ∧
      (∀ mu : V → ℝ, (∑ i, mu i = 1) →
        (∀ j, ∑ i, mu i * Q i j = mu j) → mu = pi) ∧
      0 < kappa ∧ kappa ≤ 1 ∧ (∃ i j, Q i j = kappa) ∧
      (∀ i j, 0 < Q i j → kappa ≤ Q i j) ∧
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
        ∃ K : (V → ℂ) →L[ℂ] (V → ℂ), IsProjectedInverse Q pi lam K ∧
          ‖EuclideanInverse.conjugate K‖ ≤
            Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V) := by
  obtain ⟨pi,hpi,hpisum,hstationary⟩ := stationary_probability external Q hQ hrow hc
  obtain ⟨kappa,hk0,hk1,hattain,hs⟩ := positive_minimum Q hQ hrow
  have hall (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :=
    BulkRestricted.projected_inverse_bound (fun i j => 0 < Q i j) hc Q hQ hrow
      kappa hk0 hk1 hs pi (fun i => (hpi i).le) hpisum hstationary lam hl0 hl1
  have hbound (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
      ∃ K : (V → ℂ) →L[ℂ] (V → ℂ), IsProjectedInverse Q pi lam K ∧
        ‖EuclideanInverse.conjugate K‖ ≤
          Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V) := by
    obtain ⟨K,h1,h2,h3,h4,h5⟩ := hall lam hl0 hl1
    exact ⟨K,⟨h1,h2,h3,h4⟩,h5⟩
  obtain ⟨K,hK,_⟩ := hbound 1 (by norm_num) le_rfl
  exact ⟨pi,kappa,hpi,hpisum,hstationary,stationary_unique Q pi K hK,
    hk0,hk1,hattain,hs,hbound⟩

end NonSymmetricDyson.Full.BulkMarkovComplete
