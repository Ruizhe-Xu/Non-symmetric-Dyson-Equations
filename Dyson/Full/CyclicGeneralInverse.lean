import Dyson.Full.CyclicGeneral

/-! Exact inverse and resonance criterion for every directed cycle. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set Fin.NatCast

namespace NonSymmetricDyson.Full.CyclicGeneral

variable (d : ℕ) [NeZero d]

open CyclicExample (scalar)

theorem scalar_dyson {z : ℂ} (hm : 0 < (scalar z).im) :
    BasicEstimates.IsDysonSolution (cycle d) (fun _ => 0) z (fun _ => scalar z) := by
  have hm0 : scalar z ≠ 0 := by intro he; simp [he] at hm
  intro i
  change -(scalar z)⁻¹ = z-(0:ℂ)+Model.action (cycle d) (fun _ => scalar z) i
  rw [cycle_action, sub_zero]
  apply (mul_left_cancel₀ hm0)
  simp only [mul_neg, mul_inv_cancel₀ hm0]
  linear_combination -(CyclicExample.scalar_quadratic z)

theorem canonical_eq_scalar {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im) :
    GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d) z =
      fun _ => scalar z := by
  exact GlobalWellPosedness.solution_eq_of_upper_solution (fun _ => 0)
    (cycle_nonnegative d) hz (fun _ => hm) (scalar_dyson d hm)

include d in
theorem scalar_norm_lt_one {z : ℂ} (hz : 0 < z.im) (hm : 0 < (scalar z).im) :
    ‖scalar z‖ < 1 := by
  have he := BasicEstimates.imaginary_part_identity_sq_norm (scalar_dyson d hm) (0 : Fin d)
  have hh : ∑ j, cycle d 0 j * (scalar z).im = (scalar z).im := by
    rw [← Finset.sum_mul, cycle_row_sum, one_mul]
  change (scalar z).im / ‖scalar z‖^2 = z.im + ∑ j, cycle d 0 j * (scalar z).im at he
  rw [hh] at he
  have hn : 0 < ‖scalar z‖^2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro he
    simp [he] at hm
  have he' := (div_eq_iff hn.ne').mp he
  have hpos := mul_pos hz hn
  have hh : (scalar z).im*‖scalar z‖^2 < (scalar z).im := by nlinarith
  have hs : ‖scalar z‖^2 < 1 := (mul_lt_mul_left hm).mp (by simpa using hh)
  nlinarith [norm_nonneg (scalar z)]

theorem scalar_denominator_ne_zero {z : ℂ} (hz : 0 < z.im)
    (hm : 0 < (scalar z).im) : 1-(scalar z^2)^d ≠ 0 := by
  have hn := scalar_norm_lt_one d hz hm
  have hp : ‖scalar z‖^(2*d) < 1 :=
    pow_lt_one₀ (norm_nonneg _) hn (Nat.mul_ne_zero (by decide) (NeZero.ne d))
  intro he
  have hs := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_one, norm_pow, ← pow_mul] at hs
  linarith

def canonicalInverseNorm (z : ℂ) (hz : 0 < z.im) : ℝ :=
  ‖EuclideanInverse.conjugate ((InteriorStability.stabilityContinuousEquiv
    (cycle_nonnegative d) hz
    (GlobalWellPosedness.solution_upper (fun _ => 0) (cycle_nonnegative d) hz)
    (GlobalWellPosedness.solution_equation (fun _ => 0) (cycle_nonnegative d) hz)).symm.toContinuousLinearMap)‖

/-- The geometric formula is the genuine inverse of any corresponding
continuous linear equivalence, with the ordinary Euclidean operator norm. -/
theorem inverse_explicit (e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) (q : ℂ)
    (he : ∀ u i, e u i = u i-q*u (i+1)) (hd : 1-q^d ≠ 0) :
    EuclideanInverse.conjugate e.symm.toContinuousLinearMap =
      (1-q^d)⁻¹ • numerator d q := by
  let T : Space d →L[ℂ] Space d := EuclideanInverse.conjugate e.toContinuousLinearMap
  let R : Space d →L[ℂ] Space d := EuclideanInverse.conjugate e.symm.toContinuousLinearMap
  have hT : T = 1-q • shift₂ d := by
    ext u i
    change e (WithLp.ofLp u) i = u i-q*(shift₂ d u) i
    rw [shift₂_apply]
    exact he (WithLp.ofLp u) i
  have hTR : T*R=1 := by
    ext u i
    exact congrFun (e.apply_symm_apply (WithLp.ofLp u)) i
  have hPT : ((1-q^d)⁻¹ • numerator d q)*T=1 := by
    rw [hT, smul_mul_assoc, numerator_identity_right, smul_smul, inv_mul_cancel₀ hd, one_smul]
  change R = _
  calc
    R = (1 : Space d →L[ℂ] Space d)*R := by simp
    _ = (((1-q^d)⁻¹ • numerator d q)*T)*R := by rw [hPT]
    _ = ((1-q^d)⁻¹ • numerator d q)*(T*R) := mul_assoc _ _ _
    _ = _ := by rw [hTR, mul_one]

theorem canonical_inverse_formula {z : ℂ} (hz : 0 < z.im)
    (hm : 0 < (scalar z).im) :
    canonicalInverseNorm d z hz = ‖numerator d (scalar z^2)‖ / ‖1-(scalar z^2)^d‖ := by
  let e := InteriorStability.stabilityContinuousEquiv (cycle_nonnegative d) hz
    (GlobalWellPosedness.solution_upper (fun _ => 0) (cycle_nonnegative d) hz)
    (GlobalWellPosedness.solution_equation (fun _ => 0) (cycle_nonnegative d) hz)
  have he (u : Fin d → ℂ) (i : Fin d) : e u i = u i-scalar z^2*u (i+1) := by
    change InteriorStability.stabilityOperator (cycle d)
      (GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d) z) u i = _
    rw [canonical_eq_scalar d hz hm]
    change u i-scalar z^2*Model.action (cycle d) u i = _
    rw [cycle_action]
  change ‖EuclideanInverse.conjugate e.symm.toContinuousLinearMap‖ = _
  rw [inverse_explicit d e (scalar z^2) he (scalar_denominator_ne_zero d hz hm),
    norm_smul, norm_inv]
  ring

/-- Exactly the roots `q^d=1` make the boundary stability operator singular. -/
theorem resonance_iff (q : ℂ) :
    (∃ v : Space d, v ≠ 0 ∧ (1-q • shift₂ d) v = 0) ↔ q^d=1 := by
  constructor
  · rintro ⟨v,hv,he⟩
    by_contra hq
    have hd : 1-q^d ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
    have h := congrArg (fun f : Space d →L[ℂ] Space d => f v)
      (numerator_identity_right d q)
    change numerator d q ((1-q • shift₂ d) v) = (1-q^d) • v at h
    rw [he, map_zero] at h
    exact hv ((smul_eq_zero.mp h.symm).resolve_left hd)
  · intro hq
    have hq0 : q ≠ 0 := by
      intro he
      rw [he, zero_pow (NeZero.ne d)] at hq
      exact zero_ne_one hq
    let v : Space d := WithLp.toLp 2 (eigenvector d q⁻¹)
    refine ⟨v, ?_, ?_⟩
    · intro he
      exact eigenvector_nonzero d q⁻¹ (congrArg WithLp.ofLp he)
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply]
      change v-q • shift₂ d (WithLp.toLp 2 (eigenvector d q⁻¹)) = 0
      rw [shift₂_eigenvector d q⁻¹ (by simp [hq]), smul_smul,
        mul_inv_cancel₀ hq0, one_smul, sub_self]

end NonSymmetricDyson.Full.CyclicGeneral
