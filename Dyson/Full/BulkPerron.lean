import Dyson.Full.BulkAlgebra
import Dyson.Resonance
import Mathlib

/-!
The general Perron--Frobenius simplicity theorem is an explicitly retained
external theorem. The signed eigenvector transfer, normalized left functional,
kernel projection and annihilation identities are proved on actual matrices.
-/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.BulkPerron
universe u
variable {V : Type u} [Fintype V]

/-- Generic finite-matrix Perron--Frobenius theorem at a supplied positive
eigenvector, including simplicity over ℂ. This is a standard external input;
it makes no reference to Dyson solutions or bipartite graphs. -/
def PerronLeftAndSimple : Prop :=
  ∀ {V : Type u} [Fintype V] [Nonempty V]
    (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < A i j))
    (q : V → ℝ) (hq : ∀ i, 0 < q i)
    (heig : ∀ i, ∑ j, A i j * q j = q i),
    ∃ l : V → ℝ, (∀ i, 0 < l i) ∧
      (∀ j, ∑ i, l i * A i j = l j) ∧
      ∀ x : V → ℂ, Model.action A x = x →
        ∃ c : ℂ, x = c • (fun i => (q i : ℂ))

def signMul (t x : V → ℂ) : V → ℂ := fun i => t i * x i

theorem signMul_involution (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1) (x : V → ℂ) :
    signMul t (signMul t x) = x := by
  funext i
  dsimp [signMul]
  calc
    t i * (t i * x i) = t i ^ 2 * x i := by ring
    _ = x i := by rw [ht i, one_mul]

theorem signed_minus_one_eigenspace (A : Matrix V V ℝ) (t q : V → ℂ)
    (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, A i j ≠ 0 → t j = -t i)
    (hsimple : ∀ x : V → ℂ, Model.action A x = x → ∃ c : ℂ, x = c • q)
    (x : V → ℂ) (hx : Model.action A x = -x) :
    ∃ c : ℂ, x = c • signMul t q := by
  have hplus : Model.action A (signMul t x) = signMul t x := by
    funext i
    have hanti := BulkAlgebra.action_anticommutes_of_support A t hs x i
    rw [hx] at hanti
    simpa [signMul] using hanti
  obtain ⟨c, hc⟩ := hsimple (signMul t x) hplus
  refine ⟨c, ?_⟩
  have he := congrArg (signMul t) hc
  rw [signMul_involution t ht] at he
  rw [he]
  funext i
  simp [signMul, mul_comm, mul_left_comm]

def pairing (p : V → ℂ) : (V → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, p i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem pairing_action (A : Matrix V V ℝ) (p x : V → ℂ) :
    pairing p (Model.action A x) = pairing (Model.action A.transpose p) x := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, Model.action_apply,
    Finset.mul_sum, Finset.sum_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

def plusOperator (A : Matrix V V ℝ) : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
  LinearMap.id + Model.action A

/-- Concrete normalized deflation data for `I + A` on a bipartite matrix.
The left functional and right null vector are explicitly constructed from
positive Perron vectors and the diagonal sign. -/
theorem signed_kernel_data [Nonempty V]
    (A : Matrix V V ℝ) (q l : V → ℝ) (t : V → ℂ)
    (hq : ∀ i, 0 < q i) (hl : ∀ i, 0 < l i)
    (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, A i j ≠ 0 → t j = -t i)
    (hleft : ∀ j, ∑ i, l i * A i j = l j)
    (hsimple : ∀ x : V → ℂ, Model.action A x = x →
      ∃ c : ℂ, x = c • (fun i => (q i : ℂ))) :
    ∃ phi : (V → ℂ) →L[ℂ] ℂ,
      phi (signMul t (fun i => (q i : ℂ))) = 1 ∧
      phi (signMul t (fun i => (q i : ℂ) ^ 2)) ≠ 0 ∧
      (∀ x, phi (plusOperator A x) = 0) ∧
      ∀ x, plusOperator A x = 0 →
        x = phi x • signMul t (fun i => (q i : ℂ)) := by
  let qC : V → ℂ := fun i => (q i : ℂ)
  let lC : V → ℂ := fun i => (l i : ℂ)
  let p : V → ℂ := signMul t lC
  let D : ℂ := ∑ i, (l i : ℂ) * (q i : ℂ)
  have hDreal : 0 < ∑ i, l i * q i := by
    apply Finset.sum_pos
    · intro i _
      exact mul_pos (hl i) (hq i)
    · exact Finset.univ_nonempty
  have hD : D ≠ 0 := by
    have he : D = ((∑ i, l i * q i : ℝ) : ℂ) := by simp [D]
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hDreal)
  have hpq : pairing p (signMul t qC) = D := by
    change (∑ i, (t i * (l i : ℂ)) * (t i * (q i : ℂ))) = _
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = t i ^ 2 * ((l i : ℂ) * (q i : ℂ)) := by ring
      _ = _ := by rw [ht i, one_mul]
  have hleftC : Model.action A.transpose lC = lC := by
    funext j
    have hh := congrArg (fun r : ℝ => (r : ℂ)) (hleft j)
    simpa [Model.action_apply, lC, mul_comm] using hh
  have htranspose (i j : V) (ha : A.transpose i j ≠ 0) : t j = -t i := by
    have hh := hs j i ha
    linear_combination hh
  have hp : Model.action A.transpose p = -p := by
    funext i
    have hh := BulkAlgebra.action_anticommutes_of_support A.transpose t htranspose lC i
    rw [hleftC] at hh
    simpa [p, signMul] using hh
  let phiL : (V → ℂ) →ₗ[ℂ] ℂ := D⁻¹ • pairing p
  let phi : (V → ℂ) →L[ℂ] ℂ := phiL.toContinuousLinearMap
  have hphi (x : V → ℂ) : phi x = D⁻¹ * pairing p x := rfl
  have hnorm : phi (signMul t qC) = 1 := by
    rw [hphi, hpq, inv_mul_cancel₀ hD]
  have hopen : phi (signMul t (fun i => (q i : ℂ) ^ 2)) ≠ 0 := by
    rw [hphi]
    apply mul_ne_zero (inv_ne_zero hD)
    have he : pairing p (signMul t (fun i => (q i : ℂ) ^ 2)) =
        ((∑ i, l i * q i ^ 2 : ℝ) : ℂ) := by
      simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, p, signMul, lC,
        Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = t i ^ 2 * ((l i : ℂ) * (q i : ℂ) ^ 2) := by ring
        _ = _ := by rw [ht i, one_mul]
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt
      (BulkAlgebra.left_pairing_square_positive l q hl hq))
  refine ⟨phi, hnorm, hopen, ?_, ?_⟩
  · intro x
    rw [hphi]
    have hz : pairing p (plusOperator A x) = 0 := by
      change pairing p (x + Model.action A x) = 0
      rw [map_add, pairing_action, hp]
      simp [pairing]
    rw [hz, mul_zero]
  · intro x hx
    have heig : Model.action A x = -x := by
      change x + Model.action A x = 0 at hx
      exact eq_neg_of_add_eq_zero_right hx
    obtain ⟨c, hc⟩ := signed_minus_one_eigenspace A t qC ht hs hsimple x heig
    have hcphi : phi x = c := by
      rw [hc, map_smul, hnorm, smul_eq_mul, mul_one]
    rw [hcphi]
    exact hc

theorem signed_kernel_data_of_perron [Nonempty V]
    (external : PerronLeftAndSimple.{u})
    (A : Matrix V V ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < A i j))
    (q : V → ℝ) (hq : ∀ i, 0 < q i)
    (heig : ∀ i, ∑ j, A i j * q j = q i)
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, A i j ≠ 0 → t j = -t i) :
    ∃ phi : (V → ℂ) →L[ℂ] ℂ,
      phi (signMul t (fun i => (q i : ℂ))) = 1 ∧
      phi (signMul t (fun i => (q i : ℂ) ^ 2)) ≠ 0 ∧
      (∀ x, phi (plusOperator A x) = 0) ∧
      ∀ x, plusOperator A x = 0 →
        x = phi x • signMul t (fun i => (q i : ℂ)) := by
  obtain ⟨l, hl, hleft, hsimple⟩ := external (V := V) A hA hc q hq heig
  exact signed_kernel_data A q l t hq hl ht hs hleft hsimple

end NonSymmetricDyson.Full.BulkPerron
