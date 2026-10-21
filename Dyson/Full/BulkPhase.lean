import Dyson.Full.BulkShortest
import Dyson.Full.BulkVariance
import Dyson.PhaseDefect
import Dyson.MarkovStability

noncomputable section
open scoped BigOperators Classical

namespace NonSymmetricDyson.Full.BulkPhase
open Resonance
variable {V : Type*} [Fintype V]

/-- Quantitative propagation of a nonnegative loss along a directed path. -/
theorem path_loss (E : V → V → Prop) (h : V → ℝ) (eps kappa : ℝ)
    (heps : 0 ≤ eps) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (hedge : ∀ i j, E i j → kappa * h j ≤ h i + 2 * eps)
    {a b : V} (p : Walk E a b) :
    kappa ^ BulkShortest.length p * h b ≤
      h a + 2 * (BulkShortest.length p : ℝ) * eps := by
  induction p with
  | nil => simp [BulkShortest.length]
  | @cons a b c hab rest ih =>
    have hm := mul_le_mul_of_nonneg_left ih hk0
    have he := hedge a b hab
    have hn : 0 ≤ 2 * (BulkShortest.length rest : ℝ) * eps := by positivity
    have hs := mul_le_mul_of_nonneg_right hk1 hn
    simp only [BulkShortest.length, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem uniform_loss (E : V → V → Prop) (hc : StronglyConnected E)
    (h : V → ℝ) (hh : ∀ i, 0 ≤ h i) (eps kappa : ℝ)
    (heps : 0 ≤ eps) (hk0 : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (hedge : ∀ i j, E i j → kappa * h j ≤ h i + 2 * eps)
    (root : V) (hr : h root = 0) (i : V) :
    kappa ^ (Fintype.card V - 1) * h i ≤ 2 * (Fintype.card V : ℝ) * eps := by
  obtain ⟨p, hp⟩ := BulkShortest.connected_short_walk hc root i
  have hl := path_loss E h eps kappa heps hk0 hk1 hedge p
  rw [hr, zero_add] at hl
  have hlen : BulkShortest.length p ≤ Fintype.card V - 1 := by omega
  have hpw := pow_le_pow_of_le_one hk0 hk1 hlen
  have hdim : (BulkShortest.length p : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast le_of_lt hp
  calc
    _ ≤ kappa ^ BulkShortest.length p * h i := mul_le_mul_of_nonneg_right hpw (hh i)
    _ ≤ 2 * (BulkShortest.length p : ℝ) * eps := hl
    _ ≤ 2 * (Fintype.card V : ℝ) * eps := by nlinarith

theorem exists_norm_maximum (w : V → ℂ) (hw : ‖w‖ = 1) :
    ∃ root, ‖w root‖ = 1 := by
  by_contra h
  have hall : ∀ i, ‖w i‖ < 1 := by
    intro i
    have hle : ‖w i‖ ≤ 1 := by simpa [hw] using norm_le_pi_norm w i
    exact lt_of_le_of_ne hle (fun hi => h ⟨i, hi⟩)
  have hn : ‖w‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr hall
  simpa [hw] using hn

theorem normalized_difference (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ)‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hxc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxn
  have hyc : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyn
  have hid : x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ) =
      (x - y) / (‖x‖ : ℂ) +
        (y / (‖y‖ : ℂ)) * (((‖y‖ - ‖x‖ : ℝ) : ℂ) / (‖x‖ : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ ‖(x - y) / (‖x‖ : ℂ)‖ +
        ‖(y / (‖y‖ : ℂ)) * (((‖y‖ - ‖x‖ : ℝ) : ℂ) / (‖x‖ : ℂ))‖ := norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      simp only [norm_div, norm_mul, Complex.norm_real, norm_norm,
        Real.norm_eq_abs, abs_norm, div_self hyn, one_mul]
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_right _ (norm_nonneg x)
      simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

def normalize (w : ℂ) (hw : w ≠ 0) : Circle :=
  ⟨w / (‖w‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg w),
      norm_ne_zero_iff.mpr hw]⟩

theorem delta_le_edgeDefect (E : V → V → Prop) (u gamma : V → Circle) :
    PhaseDefect.delta E u ≤ PhaseDefect.edgeDefect E u gamma :=
  csInf_le ⟨0, by rintro y ⟨g, rfl⟩; exact PhaseDefect.edgeDefect_nonnegative E u g⟩
    (Set.mem_range_self gamma)

theorem delta_le_two (E : V → V → Prop) (u : V → Circle) :
    PhaseDefect.delta E u ≤ 2 := by
  apply (delta_le_edgeDefect E u (fun _ => 1)).trans
  unfold PhaseDefect.edgeDefect
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro e
  change ‖(u e.val.1 : ℂ) - (((1 : Circle)⁻¹ * 1 : Circle) : ℂ)‖ ≤ 2
  calc
    _ ≤ ‖(u e.val.1 : ℂ)‖ + ‖(((1 : Circle)⁻¹ * 1 : Circle) : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Circle.norm_coe]

theorem weighted_pi_norm_sq_le {J : Type*} [Fintype J]
    (f : J → ℂ) (K A : ℝ) (hK : 0 < K) (hA : 0 ≤ A)
    (h : ∀ j, K * ‖f j‖ ^ 2 ≤ A) : K * ‖f‖ ^ 2 ≤ A := by
  have had : 0 ≤ A / K := div_nonneg hA (le_of_lt hK)
  have hs := Real.sq_sqrt had
  have hn : ‖f‖ ≤ Real.sqrt (A / K) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    have hj : ‖f j‖ ^ 2 ≤ A / K := (le_div_iff₀ hK).mpr (by nlinarith [h j])
    nlinarith [norm_nonneg (f j), Real.sqrt_nonneg (A / K)]
  have hn' : ‖f‖ ^ 2 ≤ A / K := by
    nlinarith [norm_nonneg f, Real.sqrt_nonneg (A / K)]
  have hh := (le_div_iff₀ hK).mp hn'
  nlinarith

theorem normalized_edge_error (u : Circle) (x y : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hhalf : (1 / 2 : ℝ) ≤ ‖x‖) :
    ‖(u : ℂ) - (((normalize x hx)⁻¹ * normalize y hy : Circle) : ℂ)‖ ≤
      4 * ‖y - (u : ℂ) * x‖ := by
  let gx : ℂ := (normalize x hx : ℂ)
  let gy : ℂ := (normalize y hy : ℂ)
  have hgx : ‖gx‖ = 1 := Circle.norm_coe _
  have hgx0 : gx ≠ 0 := by intro h; simp [h] at hgx
  have hu0 : (u : ℂ) ≠ 0 := by intro h; have := Circle.norm_coe u; simp [h] at this
  have heq : ‖(u : ℂ) - gx⁻¹ * gy‖ = ‖(u : ℂ) * gx - gy‖ := by
    have hm : ((u : ℂ) - gx⁻¹ * gy) * gx = (u : ℂ) * gx - gy := by
      field_simp
    rw [← hm, norm_mul, hgx, mul_one]
  change ‖(u : ℂ) - gx⁻¹ * gy‖ ≤ _
  rw [heq]
  have hd := normalized_difference ((u : ℂ) * x) y (mul_ne_zero hu0 hx) hy
  have hnorm : ‖(u : ℂ) * x‖ = ‖x‖ := by rw [norm_mul, Circle.norm_coe, one_mul]
  rw [hnorm] at hd
  have hid : (u : ℂ) * gx = (u : ℂ) * x / (‖x‖ : ℂ) := by
    dsimp [gx, normalize]
    ring
  rw [hid]
  change ‖(u : ℂ) * x / (‖x‖ : ℂ) - y / (‖y‖ : ℂ)‖ ≤ _
  apply hd.trans
  rw [norm_sub_rev]
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
  nlinarith [norm_nonneg (y - (u : ℂ) * x)]

/-- The squared phase defect is bounded by the residual at λ = 1.
The exponent obtained here is `d`; weakening it gives the paper's `2d`.
All graph and convexity estimates are proved in the imported helper modules. -/
theorem unit_vector_phase_defect (E : V → V → Prop) (hc : StronglyConnected E)
    (Q : Matrix V V ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa ≤ 1)
    (hsupport : ∀ i j, E i j → kappa ≤ Q i j)
    (u : V → Circle) (w : V → ℂ) (hw : ‖w‖ = 1)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hres : ∀ i, ‖(u i : ℂ) * w i - Model.action Q w i‖ ≤ eps) :
    kappa ^ Fintype.card V * (PhaseDefect.delta E u) ^ 2 ≤
      64 * (Fintype.card V : ℝ) * eps := by
  obtain ⟨root, hroot⟩ := exists_norm_maximum w hw
  have hd : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  have hdR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hd
  have hpow : 0 < kappa ^ Fintype.card V := pow_pos hk0 _
  have hpow' : 0 ≤ kappa ^ (Fintype.card V - 1) := pow_nonneg (le_of_lt hk0) _
  have hpow1 : kappa ^ (Fintype.card V - 1) ≤ 1 := pow_le_one₀ (le_of_lt hk0) hk1
  have hwle (i : V) : ‖w i‖ ≤ 1 := by simpa [hw] using norm_le_pi_norm w i
  let loss (i : V) := 1 - ‖w i‖ ^ 2
  have hloss (i : V) : 0 ≤ loss i := by
    dsimp [loss]
    nlinarith [norm_nonneg (w i), hwle i]
  have hz (i : V) : ‖(u i : ℂ) * w i‖ = ‖w i‖ := by
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hedge (i j : V) (hij : E i j) :
      kappa * loss j ≤ loss i + 2 * eps ∧
      kappa * ‖w j - (u i : ℂ) * w i‖ ^ 2 ≤ loss i + 2 * eps := by
    have hh := BulkVariance.edge_loss_and_alignment (Q i) (hQ i) (hrow i)
      w ((u i : ℂ) * w i) eps kappa hwle (by simpa [hz] using hwle i)
      (hres i) j (hsupport i j hij) hk0
    simpa only [hz] using hh
  have hunif (i : V) :
      kappa ^ (Fintype.card V - 1) * loss i ≤ 2 * (Fintype.card V : ℝ) * eps :=
    uniform_loss E hc loss hloss eps kappa heps (le_of_lt hk0) hk1
      (fun i j hij => (hedge i j hij).1) root (by simp [loss, hroot]) i
  have hpoweq : kappa ^ Fintype.card V = kappa ^ (Fintype.card V - 1) * kappa := by
    have hdim : Fintype.card V = Fintype.card V - 1 + 1 := by omega
    conv_lhs => rw [hdim, pow_succ]
  have hlosspow (i : V) :
      kappa ^ Fintype.card V * loss i ≤ 2 * (Fintype.card V : ℝ) * eps := by
    have hp := pow_le_pow_of_le_one (le_of_lt hk0) hk1
      (Nat.sub_le (Fintype.card V) 1)
    exact (mul_le_mul_of_nonneg_right hp (hloss i)).trans (hunif i)
  have halign (i j : V) (hij : E i j) :
      kappa ^ Fintype.card V * ‖w j - (u i : ℂ) * w i‖ ^ 2 ≤
        4 * (Fintype.card V : ℝ) * eps := by
    have hh := mul_le_mul_of_nonneg_left (hedge i j hij).2 hpow'
    have hs := mul_le_mul_of_nonneg_right hpow1 heps
    rw [hpoweq]
    nlinarith [hunif i]
  by_cases hlarge : kappa ^ Fintype.card V ≤ 8 * (Fintype.card V : ℝ) * eps
  · have hdel := delta_le_two E u
    have hdel0 := PhaseDefect.delta_nonnegative E u
    have hsq : (PhaseDefect.delta E u) ^ 2 ≤ 4 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hsq (le_of_lt hpow)
    nlinarith
  · have hsmall : 8 * (Fintype.card V : ℝ) * eps < kappa ^ Fintype.card V :=
      lt_of_not_ge hlarge
    have hhalf (i : V) : (1 / 2 : ℝ) ≤ ‖w i‖ := by
      have hh := hlosspow i
      dsimp [loss] at hh
      have hquarter : 1 - ‖w i‖ ^ 2 < 1 / 4 := by nlinarith
      nlinarith [norm_nonneg (w i)]
    have hw0 (i : V) : w i ≠ 0 := by
      intro he
      have hh := hhalf i
      norm_num [he] at hh
    let gamma (i : V) := normalize (w i) (hw0 i)
    have herrors (e : PhaseDefect.Edge E) :
        kappa ^ Fintype.card V * ‖PhaseDefect.edgeError E u gamma e‖ ^ 2 ≤
          64 * (Fintype.card V : ℝ) * eps := by
      have hn := normalized_edge_error (u e.val.1) (w e.val.1) (w e.val.2)
        (hw0 _) (hw0 _) (hhalf _)
      change ‖PhaseDefect.edgeError E u gamma e‖ ≤
        4 * ‖w e.val.2 - (u e.val.1 : ℂ) * w e.val.1‖ at hn
      have hs : ‖PhaseDefect.edgeError E u gamma e‖ ^ 2 ≤
          16 * ‖w e.val.2 - (u e.val.1 : ℂ) * w e.val.1‖ ^ 2 := by
        nlinarith [norm_nonneg (PhaseDefect.edgeError E u gamma e),
          norm_nonneg (w e.val.2 - (u e.val.1 : ℂ) * w e.val.1)]
      have hp := mul_le_mul_of_nonneg_left hs (le_of_lt hpow)
      nlinarith [halign e.val.1 e.val.2 e.property]
    have hnorm := weighted_pi_norm_sq_le (PhaseDefect.edgeError E u gamma)
      (kappa ^ Fintype.card V) (64 * (Fintype.card V : ℝ) * eps)
      hpow (by positivity) herrors
    have hdelta := delta_le_edgeDefect E u gamma
    have hd0 := PhaseDefect.delta_nonnegative E u
    have hs : (PhaseDefect.delta E u) ^ 2 ≤ (PhaseDefect.edgeDefect E u gamma) ^ 2 := by
      nlinarith [PhaseDefect.edgeDefect_nonnegative E u gamma]
    exact (mul_le_mul_of_nonneg_left hs (le_of_lt hpow)).trans hnorm

end NonSymmetricDyson.Full.BulkPhase
