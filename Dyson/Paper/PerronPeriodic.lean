import Mathlib
import Dyson.Model
import Dyson.Full.ClassicalFrobenius

/-! Original proof of the Markov inverse lemma: cyclic class masses,
weighted orthogonality, and the actual periodic Fourier vectors. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Finset

namespace NonSymmetricDyson.Paper.Perron

variable {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]

def classMass (π : ι → ℝ) (cls : ι → ZMod p) (c : ZMod p) : ℝ :=
  ∑ i, if cls i = c then π i else 0

def classMean (π : ι → ℝ) (cls : ι → ZMod p) (c : ZMod p) (x : ι → ℂ) : ℂ :=
  ∑ i, if cls i = c then (π i : ℂ)*x i else 0

def weightedInner (π : ι → ℝ) (x y : ι → ℂ) : ℂ :=
  ∑ i, (π i : ℂ)*conj (x i)*y i

def periodVector (cls : ι → ZMod p) (k : ZMod p) (i : ι) : ℂ :=
  ZMod.stdAddChar (-(k*cls i))

def ClassConstant (cls : ι → ZMod p) (x : ι → ℂ) : Prop :=
  ∃ a : ZMod p → ℂ, ∀ i, x i = a (cls i)

def ClassCentered (π : ι → ℝ) (cls : ι → ZMod p) (x : ι → ℂ) : Prop :=
  ∀ c, classMean π cls c x = 0

theorem sum_classMass (π : ι → ℝ) (cls : ι → ZMod p) :
    ∑ c, classMass π cls c = ∑ i, π i := by
  unfold classMass
  rw [Finset.sum_comm]
  simp

theorem sum_over_classes (π : ι → ℝ) (cls : ι → ZMod p) (a : ZMod p → ℂ) :
    (∑ i, (π i:ℂ)*a (cls i)) = ∑ c, (classMass π cls c:ℂ)*a c := by
  simp only [classMass, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Exact cyclic transport of weighted means, the computation in Step 3. -/
theorem classMean_action (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hstat : ∀ j, ∑ i, π i*Q i j = π j)
    (hsupport : ∀ i j, 0 < Q i j → cls j = cls i+1)
    (c : ZMod p) (x : ι → ℂ) :
    classMean π cls c (Model.action Q x) = classMean π cls (c+1) x := by
  have hind (i j : ι) :
      (if cls i=c then (π i:ℂ)*(Q i j:ℂ)*x j else 0) =
      (if cls j=c+1 then (π i:ℂ)*(Q i j:ℂ)*x j else 0) := by
    by_cases hq : Q i j=0
    · simp [hq]
    · have he := hsupport i j (lt_of_le_of_ne (hQ i j) (Ne.symm hq))
      have hc : cls i=c ↔ cls j=c+1 := by rw [he]; exact add_right_cancel_iff.symm
      simp [hc]
  unfold classMean
  calc
    _ = ∑ i, ∑ j, if cls i=c then (π i:ℂ)*(Q i j:ℂ)*x j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : cls i=c <;> simp [hi, Model.action_apply, Finset.mul_sum, mul_assoc]
    _ = ∑ i, ∑ j, if cls j=c+1 then (π i:ℂ)*(Q i j:ℂ)*x j else 0 := by
      simp_rw [hind]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : cls j=c+1
      · simp only [hj, if_true, ← Finset.sum_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, hstat]
      · simp [hj]

theorem classMass_next (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j=1)
    (hstat : ∀ j, ∑ i, π i*Q i j=π j)
    (hsupport : ∀ i j, 0 < Q i j → cls j=cls i+1) (c : ZMod p) :
    classMass π cls (c+1)=classMass π cls c := by
  have h := classMean_action Q π cls hQ hstat hsupport c (fun _ => 1)
  have hones : Model.action Q (fun _ => (1:ℂ))=fun _ => 1 := by
    ext i
    simp [Model.action_apply, ← Complex.ofReal_sum, hrow i]
  rw [hones] at h
  have he (b : ZMod p) : classMean π cls b (fun _ => (1:ℂ))=(classMass π cls b:ℂ) := by
    simp [classMean, classMass, apply_ite]
  rw [he, he] at h
  exact Complex.ofReal_injective h.symm

/-- Every cyclic class has exactly mass 1/p, including the aperiodic case. -/
theorem classMass_eq_inv (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j=1)
    (hstat : ∀ j, ∑ i, π i*Q i j=π j) (hprob : ∑ i, π i=1)
    (hsupport : ∀ i j, 0 < Q i j → cls j=cls i+1) (c : ZMod p) :
    classMass π cls c = (p:ℝ)⁻¹ := by
  have hnext := classMass_next Q π cls hQ hrow hstat hsupport
  have hnat : ∀ n : ℕ, classMass π cls (n:ZMod p)=classMass π cls 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, hnext] using ih
  have hall (b : ZMod p) : classMass π cls b=classMass π cls 0 := by
    simpa using hnat b.val
  have hsum : (p:ℝ)*classMass π cls 0=1 := by
    have h := sum_classMass π cls
    simpa [hall, hprob] using h
  rw [hall]
  apply mul_left_cancel₀ (show (p:ℝ)≠0 by exact_mod_cast NeZero.ne p)
  simpa using hsum

/-- The periodic directions are actual eigenvectors of Q. -/
theorem periodVector_eigen (Q : Matrix ι ι ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j=1)
    (hsupport : ∀ i j, 0 < Q i j → cls j=cls i+1) (k : ZMod p) :
    Model.action Q (periodVector cls k) =
      ZMod.stdAddChar (-k) • periodVector cls k := by
  ext i
  change (∑ j, (Q i j:ℂ)*periodVector cls k j)=_
  calc
    _ = ∑ j, (Q i j:ℂ)*(ZMod.stdAddChar (-k)*periodVector cls k i) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hq : Q i j=0
      · simp [hq]
      · rw [periodVector, hsupport i j (lt_of_le_of_ne (hQ i j) (Ne.symm hq))]
        simp only [mul_add, mul_one, neg_add, AddChar.map_add_eq_mul, periodVector]
        ring
    _ = _ := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hrow i]
      simp

theorem standard_character_sum (k : ZMod p) :
    (∑ c : ZMod p, ZMod.stdAddChar (k*c)) = if k=0 then (p:ℂ) else 0 := by
  split_ifs with hk
  · simp [hk]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hk)

/-- The Fourier vectors are orthonormal in the actual invariant weighted
inner product. This is the original equal-class-mass computation. -/
theorem periodVector_orthonormal (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (k l : ZMod p) :
    weightedInner π (periodVector cls k) (periodVector cls l) =
      if k=l then 1 else 0 := by
  have hchar (c : ZMod p) :
      conj (ZMod.stdAddChar (-(k*c)))*ZMod.stdAddChar (-(l*c)) =
        ZMod.stdAddChar ((k-l)*c) := by
    rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
      ← AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold weightedInner periodVector
  simp_rw [mul_assoc, hchar]
  rw [sum_over_classes π cls (fun c => ZMod.stdAddChar ((k-l)*c))]
  simp_rw [hmass, Complex.ofReal_inv]
  rw [← Finset.mul_sum, standard_character_sum]
  by_cases hkl : k=l
  · simp [hkl, NeZero.ne p]
  · simp [sub_ne_zero.mpr hkl, hkl]

/-- Fourier inversion gives an explicit expansion of every class-constant
vector; hence these p orthonormal vectors span exactly the period subspace. -/
theorem classConstant_fourier_expansion (cls : ι → ZMod p) (x : ι → ℂ)
    (hx : ClassConstant cls x) :
    ∃ a : ZMod p → ℂ, x=∑ k, a k • periodVector cls k := by
  obtain ⟨b, hb⟩ := hx
  let a := (ZMod.dft (N := p) (E := ℂ)).symm b
  refine ⟨a, ?_⟩
  ext i
  have h := congrFun ((ZMod.dft (N := p) (E := ℂ)).apply_symm_apply b) (cls i)
  rw [ZMod.dft_apply] at h
  rw [hb i, ← h]
  simp [a, periodVector, smul_eq_mul, mul_comm]

theorem classCentered_action (Q : Matrix ι ι ℝ) (π : ι → ℝ) (cls : ι → ZMod p)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hstat : ∀ j, ∑ i, π i*Q i j=π j)
    (hsupport : ∀ i j, 0 < Q i j → cls j=cls i+1)
    (x : ι → ℂ) (hx : ClassCentered π cls x) :
    ClassCentered π cls (Model.action Q x) := by
  intro c
  rw [classMean_action Q π cls hQ hstat hsupport]
  exact hx (c+1)

end NonSymmetricDyson.Paper.Perron
