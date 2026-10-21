import Dyson.Paper.PerronMixing
import Dyson.IrreduciblePositivity

/-! Fixed-support power minorization and invariant probability comparison.
All exponents are selected from the fixed support before varying Q. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.Perron
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem power_entry_lower_of_support (S Q : Matrix ι ι ℝ)
    (hS : ∀ i j,0≤S i j) (hQ : ∀ i j,0≤Q i j)
    (κ : ℝ) (hκ : 0≤κ) (hs : ∀ i j,0<S i j → κ≤Q i j)
    (L : ℕ) (i j : ι) (hpos : 0<(S^L) i j) : κ^L≤(Q^L) i j := by
  induction L generalizing i j with
  | zero =>
    have hij : i=j := by
      by_contra h
      simpa [Matrix.one_apply_ne h] using hpos
    subst j
    simp
  | succ L ih =>
    rw [pow_succ,Matrix.mul_apply] at hpos
    rw [show Q^(L+1)=Q^L*Q by rw [pow_succ],Matrix.mul_apply]
    obtain ⟨t,ht⟩ : ∃ t,0<(S^L) i t*S t j := by
      by_contra h
      push_neg at h
      exact (not_lt_of_ge (Finset.sum_nonpos (fun t _ => h t))) hpos
    have ha : 0<(S^L) i t := by
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (hS t j))) ht
    have hb : 0<S t j := by
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (power_nonnegative S hS L i t)
        (le_of_not_gt h))) ht
    rw [pow_succ]
    exact (mul_le_mul (ih i t ha) (hs t j hb) hκ (power_nonnegative Q hQ L i t)).trans
      (Finset.single_le_sum (fun k _ => mul_nonneg (power_nonnegative Q hQ L i k)
        (hQ k j)) (Finset.mem_univ t))

/-- The original support-only exponent: a primitive power is selected from
the fixed S, and every stochastic Q with this support obeys the same bound. -/
theorem fixed_support_periodic_minorization
    (external : Full.ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) :
    ∃ p : ℕ, ∃ hp : NeZero p, ∃ cls : Fin n → ZMod p, ∃ L : ℕ,
      0<L ∧ Function.Surjective cls ∧
      (∀ i j,0<S i j → cls j=cls i+1) ∧
      ∀ (Q : Matrix (Fin n) (Fin n) ℝ), (∀ i j,0≤Q i j) →
        ∀ κ : ℝ,0≤κ → (∀ i j,0<S i j → κ≤Q i j) →
          ∀ i j,cls i=cls j → κ^L≤(Q^L) i j := by
  obtain ⟨p,hp,cls,honto,_,hedge,_,_,hprimitive⟩ := external.cyclic n hn S hS hirr
  letI : NeZero p := ⟨hp.ne'⟩
  choose N hN hpos using hprimitive
  let M : ℕ := ∑ c : ZMod p,N c
  have hNM (c : ZMod p) : N c≤M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ c)
  have hM : 0<M := (hN 0).trans_le (hNM 0)
  refine ⟨p,inferInstance,cls,p*M,Nat.mul_pos hp hM,honto,hedge,?_⟩
  intro Q hQ κ hκ hs i j hij
  exact power_entry_lower_of_support S Q hS hQ κ hκ hs (p*M) i j
    (hpos (cls i) M (hNM (cls i)) i j rfl hij.symm)

/-- Iterating stationarity along a short support path gives the precise
probability comparison used before passing from weighted to Euclidean norm. -/
theorem stationary_coordinate_comparison {n : ℕ}
    (S Q : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hQ : ∀ i j,0≤Q i j) (π : Fin n → ℝ) (hπ : ∀ i,0≤π i)
    (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (hs : ∀ i j,0<S i j → κ≤Q i j)
    (i j : Fin n) : π i*κ^(n-1)≤π j := by
  obtain ⟨k,_,hk⟩ := hirr i j
  obtain ⟨t,ht,hpt⟩ := Manuscript.PositivityCorrection.exists_short_positive_power S hS i j ⟨k,hk⟩
  have hpow := power_entry_lower_of_support S Q hS hQ κ hκ hs t i j hpt
  have hp : κ^(n-1)≤κ^t := pow_le_pow_of_le_one hκ hκ1 (by omega)
  calc
    _ ≤ π i*(Q^t) i j := mul_le_mul_of_nonneg_left (hp.trans hpow) (hπ i)
    _ ≤ ∑ k,π k*(Q^t) k j := Finset.single_le_sum
      (fun k _ => mul_nonneg (hπ k) (power_nonnegative Q hQ t k j)) (Finset.mem_univ i)
    _ = π j := power_stationary Q π hstat t j

theorem stationary_uniform_lower {n : ℕ} (hn : 0<n)
    (S Q : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hQ : ∀ i j,0≤Q i j) (π : Fin n → ℝ) (hπ : ∀ i,0≤π i)
    (hprob : ∑ i,π i=1) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (κ : ℝ) (hκ : 0≤κ) (hκ1 : κ≤1) (hs : ∀ i j,0<S i j → κ≤Q i j)
    (j : Fin n) : κ^(n-1)/(n:ℝ)≤π j := by
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    stationary_coordinate_comparison S Q hS hirr hQ π hπ hstat κ hκ hκ1 hs i j)
  rw [← Finset.sum_mul,hprob,one_mul] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  exact (div_le_iff₀ (by exact_mod_cast hn)).mpr (by simpa [mul_comm] using h)

end NonSymmetricDyson.Paper.Perron
