import Dyson.Full.PowerGluing

/-! The large-perturbation part of the nonlinear bound is an actual uniform
real inequality, including unbounded perturbation sizes. -/
noncomputable section
namespace NonSymmetricDyson.Full.PowerGluing

/-- A bounded error is controlled by the nonlinear stability scale whenever
the perturbation is bounded away from zero and the background is bounded above.
The constant is explicit and uniform for all E ≥ ε, with no upper bound on E. -/
theorem large_error_uniform_bound {c₀ δ ε p : ℝ}
    (hc : 0 < c₀) (hδ : 0 < δ) (hε : 0 < ε) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E d R : ℝ), ε ≤ E → 0 ≤ d → d ≤ δ → R ≤ c₀ →
      R ≤ C * E / (E+d)^(1-p) := by
  let A : ℝ := c₀ / ε^p
  let c : ℝ := ε/δ
  refine ⟨A*(1+c⁻¹), ?_, ?_⟩
  · dsimp [A, c]
    positivity
  · intro E d R hE hd hdδ hR
    have hEp : 0 < ε^p := Real.rpow_pos_of_pos hε _
    have hA : 0 < A := div_pos hc hEp
    have hc' : 0 < c := div_pos hε hδ
    have hregime : c*d ≤ E := by
      calc
        c*d ≤ c*δ := mul_le_mul_of_nonneg_left hdδ hc'.le
        _ = ε := by dsimp [c]; field_simp
        _ ≤ E := hE
    have hpower : ε^p ≤ (E+d)^p :=
      Real.rpow_le_rpow hε.le (hE.trans (le_add_of_nonneg_right hd)) hp.le
    have hrough : R ≤ A*(E+d)^p := by
      apply hR.trans
      calc
        c₀ = A*ε^p := by dsimp [A]; field_simp
        _ ≤ A*(E+d)^p := mul_le_mul_of_nonneg_left hpower hA.le
    simpa only [mul_div_assoc] using
      rough_to_unified (hε.le.trans hE) hd hc' hp hA.le hregime hrough

end NonSymmetricDyson.Full.PowerGluing
