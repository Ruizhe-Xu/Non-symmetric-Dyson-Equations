import Dyson.Paper.PerronSupportGap
import Dyson.Paper.PerronInverse

/-! Original manuscript lemma Q-second-singular-gap-lambda.
The final endpoint calls the verified cyclic Fourier/Doeblin proof. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.Perron
open Full

/-- Support-uniform projected inverse, including the endpoint λ=1 with its
restricted inverse meaning. C,N are selected before Q, π, κ and λ. -/
theorem original_markov_projected_inverse
    (frobenius : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j,0≤Q i j) → (∀ i,∑ j,Q i j=1) →
      (∀ i j,0<Q i j ↔ 0<S i j) →
      ∀ π : Fin n → ℝ,(∀ i,0≤π i) → (∑ i,π i=1) →
      (∀ j,∑ i,π i*Q i j=π j) →
      ∀ κ : ℝ,0<κ → κ≤1 → (∀ i j,0<S i j → κ≤Q i j) →
      ∀ lam : ℝ,0≤lam → lam≤1 →
      ∃ K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
        BulkMarkovComplete.IsProjectedInverse Q π lam K ∧
        ‖EuclideanInverse.conjugate K‖≤C/κ^N := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨g,N,hg,hN,hgap⟩ := fixed_support_original_gap frobenius hn S hS hirr
  have hsqrt : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  refine ⟨Real.sqrt n*(2*Real.sqrt n)/g,N,by positivity,hN,?_⟩
  intro Q hQ hrow hsupp π hπ hprob hstat κ hκ hκ1 hs lam hlam hlam1
  obtain ⟨K,hK,hbound⟩ := projected_inverse_of_gap Q hrow π hπ hprob hstat
    lam (g*κ^N) (Real.sqrt n) (mul_pos hg (pow_pos hκ N)) hsqrt.le
    (hgap Q hQ hrow hsupp π hπ hprob hstat κ hκ hκ1 hs lam hlam hlam1)
  refine ⟨K,hK,?_⟩
  simp only [Fintype.card_fin] at hbound
  convert hbound using 1 <;> ring

/-- Literal source endpoint: invariant probability, uniqueness and actual
minimum positive entry are constructed, while the inverse bound comes from
original_markov_projected_inverse. -/
theorem markov_second_singular_gap
    (frobenius : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    (perron : BulkPerron.PerronLeftAndSimple.{0})
    {n : ℕ} (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j,0≤Q i j) → (∀ i,∑ j,Q i j=1) →
      (∀ i j,0<Q i j ↔ 0<S i j) →
      ∃ (π : Fin n → ℝ) (κ : ℝ),
      (∀ i,0<π i) ∧ (∑ i,π i=1) ∧ (∀ j,∑ i,π i*Q i j=π j) ∧
      (∀ μ : Fin n → ℝ,(∑ i,μ i=1) → (∀ j,∑ i,μ i*Q i j=μ j) → μ=π) ∧
      0<κ ∧ κ≤1 ∧ (∃ i j,Q i j=κ) ∧ (∀ i j,0<Q i j → κ≤Q i j) ∧
      ∀ lam : ℝ,0≤lam → lam≤1 →
      ∃ K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
        BulkMarkovComplete.IsProjectedInverse Q π lam K ∧
        ‖EuclideanInverse.conjugate K‖≤C/κ^N := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨C,N,hC,hN,hall⟩ := original_markov_projected_inverse frobenius hn S hS hirr
  refine ⟨C,N,hC,hN,?_⟩
  intro Q hQ hrow hsupp
  have he : (fun i j => 0<Q i j)=(fun i j => 0<S i j) :=
    funext (fun i => funext (fun j => propext (hsupp i j)))
  have hc : Resonance.StronglyConnected (fun i j => 0<Q i j) := by
    rw [he]
    exact Manuscript.PositivityCorrection.support_stronglyConnected_of_irreducible S hS hirr
  obtain ⟨π,hπ,hprob,hstat⟩ := BulkMarkovComplete.stationary_probability (V := Fin n) perron Q hQ hrow hc
  obtain ⟨κ,hκ,hκ1,hattain,hmin⟩ := BulkMarkovComplete.positive_minimum Q hQ hrow
  have hkS : ∀ i j,0<S i j → κ≤Q i j := fun i j hij => hmin i j ((hsupp i j).mpr hij)
  have hbound := hall Q hQ hrow hsupp π (fun i => (hπ i).le) hprob hstat κ hκ hκ1 hkS
  obtain ⟨K,hK,_⟩ := hbound 1 zero_le_one le_rfl
  exact ⟨π,κ,hπ,hprob,hstat,BulkMarkovComplete.stationary_unique Q π K hK,
    hκ,hκ1,hattain,hmin,hbound⟩

end NonSymmetricDyson.Paper.Perron
