import Dyson.Full.BulkMarkov
import Dyson.Full.BulkPerron
import Dyson.Full.Singularities
import Dyson.Full.EuclideanInverse

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkRestricted
open Resonance MarkovStability
variable {V : Type*} [Fintype V] [Nonempty V]

theorem unit_centered_bound
    (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hs : ∀ i j, E i j → kappa ≤ Q i j)
    (pi : V → ℝ) (hpi : ∀ i, 0 ≤ pi i) (hpisum : ∑ i, pi i = 1)
    (w : V → ℂ) (hw : ‖w‖ = 1) (hmean : ∑ i, (pi i : ℂ) * w i = 0)
    (eps : ℝ) (heps : 0 ≤ eps) (hres : ∀ i, ‖w i - Model.action Q w i‖ ≤ eps) :
    kappa ^ (Fintype.card V - 1) ≤ 2 * (Fintype.card V : ℝ) * eps := by
  obtain ⟨root, hroot⟩ := BulkPhase.exists_norm_maximum w hw
  let rotation : ℂ := star (w root)
  have hnrot : ‖rotation‖ = 1 := by simpa [rotation] using hroot
  let loss (i : V) := 1 - (rotation * w i).re
  have hloss (i : V) : 0 ≤ loss i := by
    have hr := (le_abs_self (rotation * w i).re).trans (Complex.abs_re_le_norm _)
    rw [norm_mul, hnrot, one_mul] at hr
    have hwle : ‖w i‖ ≤ 1 := by simpa [hw] using norm_le_pi_norm w i
    change 0 ≤ 1 - (rotation * w i).re
    linarith
  have hrootloss : loss root = 0 := by
    change 1 - (star (w root) * w root).re = 0
    rw [Complex.star_def, Complex.conj_mul', hroot]
    norm_num
  have hmeanrot : ∑ i, pi i * (rotation * w i).re = 0 := by
    have hcmean : ∑ i, (pi i : ℂ) * (rotation * w i) = 0 := by
      calc
        _ = rotation * (∑ i, (pi i : ℂ) * w i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hmean]; simp
    have hh := congrArg Complex.re hcmean
    simpa [Complex.mul_re] using hh
  have hmeanloss : ∑ i, pi i * loss i = 1 := by
    simp only [loss, mul_sub, mul_one, Finset.sum_sub_distrib, hpisum, hmeanrot, sub_zero]
  have hsum (i : V) : ∑ j, Q i j * loss j = loss i + (rotation * (w i - Model.action Q w i)).re := by
    have hh : (rotation * Model.action Q w i).re = ∑ j, Q i j * (rotation * w j).re := by
      simp only [Model.action_apply, Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [Complex.mul_re, Complex.mul_im]
      ring
    calc
      _ = 1 - ∑ j, Q i j * (rotation * w j).re := by
        simp only [loss, mul_sub, mul_one, Finset.sum_sub_distrib, hrow]
      _ = 1 - (rotation * Model.action Q w i).re := by rw [hh]
      _ = _ := by
        change _ = 1 - (rotation * w i).re + (rotation * (w i - Model.action Q w i)).re
        rw [mul_sub, Complex.sub_re]
        ring
  have hedge (i j : V) (hij : E i j) : kappa * loss j ≤ loss i + 2 * eps := by
    have hj := Finset.single_le_sum (fun j _ => mul_nonneg (hQ i j) (hloss j)) (Finset.mem_univ j)
    have hbound : (rotation * (w i - Model.action Q w i)).re ≤ eps := by
      have hh := (le_abs_self (rotation * (w i - Model.action Q w i)).re).trans
        (Complex.abs_re_le_norm _)
      rw [norm_mul, hnrot, one_mul] at hh
      exact hh.trans (hres i)
    have hlo := mul_le_mul_of_nonneg_right (hs i j hij) (hloss j)
    rw [hsum] at hj
    linarith
  have hunif (i : V) := BulkPhase.uniform_loss E hc loss hloss eps kappa
    heps hk0.le hk1 hedge root hrootloss i
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hunif i) (hpi i))
  have hl : (∑ i, pi i * (kappa ^ (Fintype.card V - 1) * loss i)) =
      kappa ^ (Fintype.card V - 1) := by
    calc
      _ = kappa ^ (Fintype.card V - 1) * ∑ i, pi i * loss i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hmeanloss, mul_one]
  have hr : (∑ i, pi i * (2 * (Fintype.card V : ℝ) * eps)) = 2 * (Fintype.card V : ℝ) * eps := by
    rw [← Finset.sum_mul, hpisum, one_mul]
  rwa [hl, hr] at hh

/-- A stronger quantitative form of the original restricted Markov lemma.
The maximum principle does not require aperiodicity or reversibility. -/
theorem centered_bound
    (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hs : ∀ i j, E i j → kappa ≤ Q i j)
    (pi : V → ℝ) (hpi : ∀ i, 0 ≤ pi i) (hpisum : ∑ i, pi i = 1)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (w : V → ℂ) (hmean : ∑ i, (pi i : ℂ) * w i = 0) :
    kappa ^ (2 * Fintype.card V) * ‖w‖ ≤
      4 * (Fintype.card V : ℝ) * ‖phaseMarkovOperator Q (fun _ => 1) lam w‖ := by
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let c : ℂ := (‖w‖ : ℂ)⁻¹
  let v : V → ℂ := c • w
  have hcn : ‖c‖ = ‖w‖⁻¹ := by simp [c, Complex.norm_real]
  have hv : ‖v‖ = 1 := by dsimp [v]; rw [norm_smul, hcn, inv_mul_cancel₀ hn.ne']
  have hvmean : ∑ i, (pi i : ℂ) * v i = 0 := by
    calc
      _ = c * (∑ i, (pi i : ℂ) * w i) := by
        simp only [v, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hmean]; simp
  let R := ‖phaseMarkovOperator Q (fun _ => 1) lam w‖
  have hres (i : V) : ‖v i - Model.action Q v i‖ ≤ 2 * R / ‖w‖ := by
    have hp := norm_le_pi_norm (phaseMarkovOperator Q (fun _ => 1) 1 v) i
    have hlem := BulkMarkov.residual_at_one Q (fun _ => 1) hQ hrow lam hl0 hl1 w
    have hnres : ‖phaseMarkovOperator Q (fun _ => 1) 1 v‖ ≤ 2 * R / ‖w‖ := by
      dsimp [v]
      rw [map_smul, norm_smul, hcn]
      have hh := mul_le_mul_of_nonneg_left hlem (inv_nonneg.mpr hn.le)
      simpa [R, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
    have hh : ‖v i - Model.action Q v i‖ ≤ ‖phaseMarkovOperator Q (fun _ => 1) 1 v‖ := by
      simpa [phaseMarkovOperator_apply, Model.action_apply] using hp
    exact hh.trans hnres
  have hunit := unit_centered_bound E hc Q hQ hrow kappa hk0 hk1 hs pi hpi hpisum
    v hv hvmean (2 * R / ‖w‖) (by positivity) hres
  have hpw : kappa ^ (2 * Fintype.card V) ≤ kappa ^ (Fintype.card V - 1) :=
    pow_le_pow_of_le_one hk0.le hk1 (by omega)
  have hh := mul_le_mul_of_nonneg_right (hpw.trans hunit) hn.le
  have he : (2 * (Fintype.card V : ℝ) * (2 * R / ‖w‖)) * ‖w‖ =
      4 * (Fintype.card V : ℝ) * R := by field_simp; ring
  rwa [he] at hh


/-- Actual projected inverse, valid also at λ=1. Its Euclidean norm has the
explicit polynomial support bound claimed in the manuscript. -/
theorem projected_inverse_bound
    (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hs : ∀ i j, E i j → kappa ≤ Q i j)
    (pi : V → ℝ) (hpi : ∀ i, 0 ≤ pi i) (hpisum : ∑ i, pi i = 1)
    (hstationary : ∀ j, ∑ i, pi i * Q i j = pi j)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ∃ K : (V → ℂ) →L[ℂ] (V → ℂ),
      K (fun _ : V => (1 : ℂ)) = 0 ∧
      (∀ x, (∑ i, (pi i : ℂ) * K x i) = 0) ∧
      (∀ x, phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam (K x) =
        x - (∑ i, (pi i : ℂ) * x i) • (fun _ : V => (1 : ℂ))) ∧
      (∀ x, K (phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam x) =
        x - (∑ i, (pi i : ℂ) * x i) • (fun _ : V => (1 : ℂ))) ∧
      ‖EuclideanInverse.conjugate K‖ ≤
        Real.sqrt (Fintype.card V) * (8 * (Fintype.card V : ℝ)) / kappa ^ (2 * Fintype.card V) := by
  let one : V → ℂ := fun _ => 1
  let ell := BulkPerron.pairing (fun i => (pi i : ℂ))
  have hell (x : V → ℂ) : ell x = ∑ i, (pi i : ℂ) * x i := rfl
  have hellone : ell one = 1 := by
    change (∑ i, (pi i : ℂ) * 1) = 1
    simp only [mul_one, ← Complex.ofReal_sum, hpisum, Complex.ofReal_one]
  have hellQ (x : V → ℂ) : ell (Model.action Q x) = ell x := by
    rw [show ell = BulkPerron.pairing (fun i => (pi i : ℂ)) from rfl,
      BulkPerron.pairing_action]
    have he : Model.action Q.transpose (fun i => (pi i : ℂ)) = fun i => (pi i : ℂ) := by
      funext j
      have hh := congrArg (fun r : ℝ => (r : ℂ)) (hstationary j)
      simpa [Model.action_apply, mul_comm] using hh
    rw [he]
  have hQone : Model.action Q one = one := by
    funext i
    change (∑ j, (Q i j : ℂ) * 1) = 1
    simp only [mul_one, ← Complex.ofReal_sum, hrow, Complex.ofReal_one]
  have hellnorm (x : V → ℂ) : ‖ell x‖ ≤ ‖x‖ := by
    rw [hell]
    calc
      _ ≤ ∑ i, ‖(pi i : ℂ) * x i‖ := norm_sum_le _ _
      _ = ∑ i, pi i * ‖x i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        simp [norm_mul, Complex.norm_real, abs_of_nonneg (hpi i)]
      _ ≤ ∑ i, pi i * ‖x‖ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm _ i) (hpi i)
      _ = ‖x‖ := by rw [← Finset.sum_mul, hpisum, one_mul]
  let F : (V → ℂ) →ₗ[ℂ] (V → ℂ) :=
    (lam : ℂ) • Model.action Q + ((1 - lam : ℝ) : ℂ) • ell.smulRight one
  have hF (x : V → ℂ) : F x = (lam : ℂ) • Model.action Q x +
      ((1 - lam : ℝ) : ℂ) • (ell x • one) := rfl
  have hFone : F one = one := by
    rw [hF, hQone, hellone, one_smul, ← add_smul]
    norm_num
  have hellF (x : V → ℂ) : ell (F x) = ell x := by
    rw [hF, map_add, map_smul, map_smul, map_smul, hellQ, hellone]
    simp only [smul_eq_mul, mul_one, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hR (x : V → ℂ) : phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam x =
      x - (lam : ℂ) • Model.action Q x := by
    funext i
    simp [phaseMarkovOperator_apply, Model.action_apply]
  have hsimp (x : V → ℂ) (hx : F x = x) : x = ell x • one := by
    let y := x - ell x • one
    have hymean : ell y = 0 := by simp [y, map_sub, map_smul, hellone]
    have hyF : F y = y := by
      dsimp only [y]
      rw [map_sub, map_smul, hFone, hx]
    have hyR : phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam y = 0 := by
      rw [hR]
      have hh := hF y
      rw [hyF, hymean, zero_smul, smul_zero, add_zero] at hh
      exact sub_eq_zero.mpr hh
    have hb := centered_bound E hc Q hQ hrow kappa hk0 hk1 hs pi hpi hpisum
      lam hl0 hl1 y hymean
    rw [hyR, norm_zero, mul_zero] at hb
    have hn : ‖y‖ = 0 := by
      have hp : 0 < kappa ^ (2 * Fintype.card V) := pow_pos hk0 _
      nlinarith [norm_nonneg y]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  obtain ⟨K0, hK0⟩ := Singularities.restricted_inverse_exists F ell one hellone hFone hellF hsimp
  let K := K0.toContinuousLinearMap
  have hKmean (x : V → ℂ) : ell (K x) = 0 := hK0.kill_left x
  have hright (x : V → ℂ) : phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam (K x) = x - ell x • one := by
    have hh := hK0.right_inverse x
    rw [hF, hK0.kill_left, zero_smul, smul_zero, add_zero] at hh
    simpa only [hR] using hh
  have hleft (x : V → ℂ) : K (phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam x) = x - ell x • one := by
    have he : phaseMarkovOperator Q (fun _ : V => (1 : ℂ)) lam x =
        (x - F x) + ((1 - lam : ℝ) : ℂ) • (ell x • one) := by
      rw [hR, hF]
      abel
    rw [he, map_add, map_smul, map_smul]
    change K0 (x - F x) + ((1 - lam : ℝ) : ℂ) • (ell x • K0 one) = _
    rw [hK0.left_inverse, hK0.kill_right, smul_zero, smul_zero, add_zero]
  have hKn : ‖K‖ ≤ 8 * (Fintype.card V : ℝ) / kappa ^ (2 * Fintype.card V) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    have hb := centered_bound E hc Q hQ hrow kappa hk0 hk1 hs pi hpi hpisum
      lam hl0 hl1 (K x) (hKmean x)
    rw [hright] at hb
    have hp : ‖x - ell x • one‖ ≤ 2 * ‖x‖ := by
      have hh := norm_sub_le x (ell x • one)
      rw [norm_smul, show ‖one‖ = 1 by simp [one], mul_one] at hh
      linarith [hellnorm x]
    have hh := hb.trans (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * (Fintype.card V : ℝ)))
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hk0 _)).mpr
    nlinarith
  refine ⟨K, hK0.kill_right, hKmean, hright, hleft, ?_⟩
  have hh := (EuclideanInverse.conjugate_norm_upper K).trans
    (mul_le_mul_of_nonneg_left hKn (Real.sqrt_nonneg _))
  simpa only [mul_div_assoc] using hh

end NonSymmetricDyson.Full.BulkRestricted
