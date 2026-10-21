import Dyson.Paper.PerronCombined
import Dyson.Paper.PerronPowers
import Dyson.Full.EuclideanInverse
import Dyson.MarkovStability

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.Perron
open Full MarkovStability

/-- Polynomial norm comparison, with an integer exponent and support-only constant. -/
theorem stationary_polynomial_norm_comparison {n : ℕ} (hn : 0<n)
    (S Q : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hQ : ∀ i j,0≤Q i j) (π : Fin n → ℝ) (hπ : ∀ i,0≤π i)
    (hprob : ∑ i,π i=1) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (hs : ∀ i j,0<S i j → κ≤Q i j)
    (x : Fin n → ℂ) :
    (κ^n/(n:ℝ))*‖x‖≤weightedNorm π x ∧
      weightedNorm π x≤Real.sqrt n*‖x‖ := by
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast hn
  let a := κ^n/(n:ℝ)
  have ha : 0≤a := by dsimp [a]; positivity
  have ha1 : a≤1 := (div_le_iff₀ hn0).mpr (by simpa using (pow_le_one₀ hκ hκ1).trans hn1)
  have hlo (i : Fin n) : a^2≤π i := by
    have hp := stationary_uniform_lower hn S Q hS hirr hQ π hπ hprob hstat κ hκ hκ1 hs i
    have hk : κ^n≤κ^(n-1) := pow_le_pow_of_le_one hκ hκ1 (by omega)
    have hh : a≤π i := (div_le_div_of_nonneg_right hk hn0.le).trans hp
    nlinarith
  have hhi (i : Fin n) : π i≤1 := by
    rw [← hprob]
    exact Finset.single_le_sum (fun j _ => hπ j) (Finset.mem_univ i)
  obtain ⟨hl,hh⟩ := weightedNorm_euclidean_bounds π (a^2) 1 (sq_nonneg a) zero_le_one hlo hhi x
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg ha] at hl
  simp only [Real.sqrt_one,one_mul] at hh
  constructor
  · exact (mul_le_mul_of_nonneg_left (Norms.sup_le_euclidean x) ha).trans hl
  · exact hh.trans (by simpa [Fintype.card_fin] using Norms.euclidean_le_sqrt_card_mul_sup x)

/-- Original Steps 1–4 combined, with the support-only quantifiers in their
original order. The gap is obtained from the cyclic Fourier and Doeblin chain. -/
theorem fixed_support_original_gap
    (external : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∃ (g : ℝ) (N : ℕ),0<g ∧ 0<N ∧
      ∀ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j,0≤Q i j) → (∀ i,∑ j,Q i j=1) →
      (∀ i j,0<Q i j ↔ 0<S i j) →
      ∀ π : Fin n → ℝ,(∀ i,0≤π i) → (∑ i,π i=1) →
      (∀ j,∑ i,π i*Q i j=π j) →
      ∀ κ : ℝ,0<κ → κ≤1 → (∀ i j,0<S i j → κ≤Q i j) →
      ∀ lam : ℝ,0≤lam → lam≤1 → ∀ x : Fin n → ℂ,
      (∑ i,(π i:ℂ)*x i=0) →
      (g*κ^N)*‖x‖≤Real.sqrt n*‖phaseMarkovOperator Q (fun _ => 1) lam x‖ := by
  obtain ⟨p,hp,cls,L,hL,honto,hedge,hpower⟩ :=
    fixed_support_periodic_minorization external hn S hS hirr
  letI : NeZero p := hp
  obtain ⟨c,hc,hc1,hgap⟩ := exists_cyclic_gap p
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  refine ⟨c/(((L:ℝ)+1)*(n:ℝ)),L+n,by positivity,by omega,?_⟩
  intro Q hQ hrow hsupp π hπ hprob hstat κ hκ hκ1 hs lam hlam hlam1 x hx
  have hclass : ∀ i j,0<Q i j → cls j=cls i+1 := fun i j hij => hedge i j ((hsupp i j).mp hij)
  have hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹ :=
    classMass_eq_inv Q π cls hQ hrow hstat hprob hclass
  have hw := original_weighted_gap Q π cls hQ hπ hrow hstat hclass hmass L hL
    (κ^L) (pow_pos hκ L) (pow_le_one₀ hκ.le hκ1)
    (hpower Q hQ κ hκ.le hs) c hc hc1 hgap lam hlam hlam1 x hx
  have hl := (stationary_polynomial_norm_comparison hn S Q hS hirr hQ π hπ hprob hstat
    κ hκ.le hκ1 hs x).1
  have hu := (stationary_polynomial_norm_comparison hn S Q hS hirr hQ π hπ hprob hstat
    κ hκ.le hκ1 hs (x-(lam:ℂ) • Model.action Q x)).2
  have he : phaseMarkovOperator Q (fun _ => 1) lam x=x-(lam:ℂ) • Model.action Q x := by
    ext i
    simp [phaseMarkovOperator_apply,Model.action_apply]
  rw [he]
  calc
    _ = (c*κ^L/((L:ℝ)+1))*((κ^n/(n:ℝ))*‖x‖) := by rw [pow_add]; field_simp
    _ ≤ (c*κ^L/((L:ℝ)+1))*weightedNorm π x :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ weightedNorm π (x-(lam:ℂ) • Model.action Q x) := hw
    _ ≤ _ := hu

end NonSymmetricDyson.Paper.Perron
