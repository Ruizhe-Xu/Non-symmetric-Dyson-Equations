import Dyson.Paper.LinearEdgeBeta
import Dyson.Full.ReducedDensityInverse

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.LinearSpectralTransfer
open Full Full.Singularities Full.SingularSpectral Full.Spectral
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The remainder exported by the actual spectral theorem is precisely the
remainder of the manuscript's scalar Taylor polynomial. -/
theorem beta_remainder {S : Matrix ι ι ℝ} {m : ι → ℂ} {p r l u : ι → ℝ}
    {K : End ι} {lam δ η ρ C : ℝ}
    {d : SimpleSpectralSplit (reducedOperator S m)}
    (h : HasDysonSpectralEstimates S m p r l u K lam δ η ρ C d) :
    ‖d.value-LinearBeta.model (1-lam) (quadraticCoefficient p l r)
      (cubicCoefficient (fun i j => ‖m i‖*S i j*‖m j‖) p l r u) δ‖≤C*(δ^3+η) := by
  convert h.2.2.2.2.2.2.2 using 1
  congr 1
  unfold LinearBeta.model
  push_cast
  ring

/-- The opposite direction of the manuscript's exact diagonal similarity:
L⁻¹=D(q)R⁻¹D(q/m²). No normal-form inverse estimate is used. -/
theorem stability_inverse_norm_transfer
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀i j,0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (q Q : ℝ) (hq : 0<q) (hQ : 0<Q) (hlo : ∀i,q≤‖m i‖) (hhi : ∀i,‖m i‖≤Q)
    (d : SimpleSpectralSplit (reducedOperator S m)) :
    ‖EuclideanInverse.stabilityInverse S a z m hS hz hm heq‖≤
      (Real.sqrt (Fintype.card ι))^2*(Q/q)*‖EuclideanInverse.conjugate d.inverse‖ := by
  have hβ := spectral_value_ne_zero_upper S a z m hS hz hm heq d
  let B : ℝ := Real.sqrt (Fintype.card ι)*‖EuclideanInverse.conjugate d.inverse‖
  have hB : 0≤B := by dsimp [B]; positivity
  have hdi : ‖d.inverse‖≤B := EuclideanInverse.conjugate_norm_lower _
  have hcoercive (v : ι → ℂ) :
      ‖v‖≤(Q*B/q)*‖InteriorStability.stabilityOperator S m v‖ := by
    let x : ι → ℂ := fun i => v i/(‖m i‖:ℂ)
    have hnz (i : ι) : (‖m i‖:ℂ)≠0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (BasicEstimates.component_ne_zero hm i)
    have hx : (fun i => (‖m i‖:ℂ)*x i)=v := by
      funext i
      dsimp [x]
      field_simp [hnz i]
    have hRx (i : ι) : reducedOperator S m x i =
        ((‖m i‖:ℂ)/(m i)^2)*InteriorStability.stabilityOperator S m v i := by
      have hh := reduced_stability_identity S m (fun i => BasicEstimates.component_ne_zero hm i) x i
      rw [hx] at hh
      rw [hh]
      field_simp [BasicEstimates.component_ne_zero hm i]
    have hrnorm : ‖reducedOperator S m x‖≤q⁻¹*‖InteriorStability.stabilityOperator S m v‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      rw [hRx,norm_mul]
      have hn : ‖(‖m i‖:ℂ)/(m i)^2‖=(‖m i‖)⁻¹ := by
        simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm,norm_pow]
        field_simp
      rw [hn]
      exact mul_le_mul (inv_anti₀ hq (hlo i)) (norm_le_pi_norm _ i) (norm_nonneg _) (by positivity)
    have hxnorm : ‖x‖≤B*(q⁻¹*‖InteriorStability.stabilityOperator S m v‖) := by
      have hh := d.inverse.le_opNorm (reducedOperator S m x)
      rw [d.inverse_left hβ x] at hh
      exact hh.trans (mul_le_mul hdi hrnorm (norm_nonneg _) hB)
    have hv : ‖v‖≤Q*‖x‖ := by
      rw [← hx]
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_norm]
      exact mul_le_mul (hhi i) (norm_le_pi_norm x i) (norm_nonneg _) hQ.le
    exact hv.trans ((mul_le_mul_of_nonneg_left hxnorm hQ.le).trans_eq (by ring))
  have ht := EuclideanInverse.stability_inverse_upper S a z m hS hz hm heq (Q*B/q)
    (by positivity) hcoercive
  exact ht.trans_eq (by dsimp [B]; ring)

end NonSymmetricDyson.Paper.LinearSpectralTransfer
