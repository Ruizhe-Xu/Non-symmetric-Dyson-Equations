import Dyson.Paper.PerronCombined
import Dyson.Paper.PerronPowers
import Dyson.Full.BulkMarkovComplete

/-! The actual inverse constructed from the original Fourier–Doeblin gap.
Only finite-dimensional algebra is reused from the backend. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.Perron
open Full Resonance MarkovStability
variable {V : Type*} [Fintype V] [Nonempty V]

/-- Finite-dimensional inverse construction from any proved centered gap. -/
theorem projected_inverse_of_gap
    (Q : Matrix V V ℝ) (hrow : ∀ i, ∑ j, Q i j = 1)
    (pi : V → ℝ) (hpi : ∀ i, 0 ≤ pi i) (hpisum : ∑ i, pi i = 1)
    (hstationary : ∀ j, ∑ i, pi i * Q i j = pi j)
    (lam b B : ℝ) (hb0 : 0<b) (hB : 0≤B)
    (hgap : ∀ w : V → ℂ,(∑ i,(pi i:ℂ)*w i)=0 →
      b*‖w‖≤B*‖phaseMarkovOperator Q (fun _ => 1) lam w‖) :
    ∃ K : (V → ℂ) →L[ℂ] (V → ℂ),
      BulkMarkovComplete.IsProjectedInverse Q pi lam K ∧
      ‖EuclideanInverse.conjugate K‖≤Real.sqrt (Fintype.card V)*(2*B/b) := by
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
    have hb := hgap y hymean
    rw [hyR, norm_zero, mul_zero] at hb
    have hn : ‖y‖ = 0 := by
      have hp : 0 < b := hb0
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
  have hKn : ‖K‖ ≤ 2 * B / b := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    have hb := hgap (K x) (hKmean x)
    rw [hright] at hb
    have hp : ‖x - ell x • one‖ ≤ 2 * ‖x‖ := by
      have hh := norm_sub_le x (ell x • one)
      rw [norm_smul, show ‖one‖ = 1 by simp [one], mul_one] at hh
      linarith [hellnorm x]
    have hh := hb.trans (mul_le_mul_of_nonneg_left hp hB)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hb0).mpr
    nlinarith
  refine ⟨K, ⟨hK0.kill_right, hKmean, hright, hleft⟩, ?_⟩
  have hh := (EuclideanInverse.conjugate_norm_upper K).trans
    (mul_le_mul_of_nonneg_left hKn (Real.sqrt_nonneg _))
  exact hh

end NonSymmetricDyson.Paper.Perron
