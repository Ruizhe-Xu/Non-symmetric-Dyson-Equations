import Dyson.Paper.CyclicModes

/-! Appendix counterexample by the original Fourier-mode route. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full Full.CyclicGeneral Full.CyclicExample
variable (d : ℕ) [NeZero d]

theorem canonical_inverse_data (z : ℂ) (hz : 0<z.im) :
    ∃ T : Space d →L[ℂ] Space d,
      ‖T‖=canonicalInverseNorm d z hz ∧
      ∀x,T ((1-(scalar z)^2 • shift₂ d) x)=x := by
  let e := InteriorStability.stabilityContinuousEquiv (cycle_nonnegative d) hz
    (GlobalWellPosedness.solution_upper (fun _ => 0) (cycle_nonnegative d) hz)
    (GlobalWellPosedness.solution_equation (fun _ => 0) (cycle_nonnegative d) hz)
  refine ⟨EuclideanInverse.conjugate e.symm.toContinuousLinearMap,rfl,?_⟩
  have hT : EuclideanInverse.conjugate e.toContinuousLinearMap=1-(scalar z)^2 • shift₂ d := by
    ext x i
    change InteriorStability.stabilityOperator (cycle d)
      (GlobalWellPosedness.solution (cycle d) (fun _ => 0) (cycle_nonnegative d) z)
      (WithLp.ofLp x) i = x i-(scalar z)^2*(shift₂ d x) i
    rw [canonical_eq_scalar_global d hz,shift₂_apply]
    change x i-(scalar z)^2*Model.action (cycle d) (WithLp.ofLp x) i = _
    rw [cycle_action]
    rfl
  intro x
  rw [←hT]
  ext i
  exact congrFun (e.symm_apply_apply (WithLp.ofLp x)) i

theorem inverse_implies_nonzero_modes (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ)
    (T : Space d →L[ℂ] Space d) (hT : ∀x,T ((1-q • shift₂ d) x)=x) :
    ∀k : Fin d,1-q*ζ^k.val≠0 := by
  intro k hk
  have hh := hT (basis d ζ hζ k)
  rw [stability_eigen,hk,zero_smul,map_zero] at hh
  have hn := congrArg norm hh
  simpa [mode_norm d ζ (hζ.norm'_eq_one (NeZero.ne d))] using hn

/-- The final inverse growth is obtained from the one small Fourier mode
and uniform separation of all other modes, without the geometric inverse. -/
theorem canonical_inverse_order_fourier (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (hi : 0<ζ.im) (hd : 3≤d) :
    ∃ c C r : ℝ,0<c ∧ 0<C ∧ 0<r ∧ ∀η : ℝ,∀hη : 0<η,η<r →
      c/η≤canonicalInverseNorm d (heightPoint (-2*ζ.re) η) (by simpa using hη) ∧
      canonicalInverseNorm d (heightPoint (-2*ζ.re) η) (by simpa using hη)≤C/η := by
  have hiinv : 0<ζ.im⁻¹ := inv_pos.mpr hi
  have hsmall := (singular_beta_height_limit d ζ hζ hi hd).eventually
    (Ioo_mem_nhds (show ζ.im⁻¹/2<ζ.im⁻¹ by linarith)
      (show ζ.im⁻¹<2*ζ.im⁻¹ by linarith))
  obtain ⟨c,hc,hother⟩ := nonsingular_modes_separated d ζ hζ hi hd
  have hone : ∀ᶠ η in 𝓝[>] (0:ℝ),η≤1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_le_const (by norm_num : (0:ℝ)<1)
  have hall := hsmall.and (hother.and hone)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hall
  let B : ℝ := 2*ζ.im+c⁻¹
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨ζ.im/2,d*B,r,half_pos hi,by positivity,hr,?_⟩
  intro η hη hηr
  have hh := hball ⟨by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hη] using hηr,hη⟩
  obtain ⟨hlo,hup⟩ := hh.1
  have hotherη := hh.2.1
  have hη1 := hh.2.2
  change ζ.im⁻¹/2<‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖/η at hlo
  change ‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖/η<2*ζ.im⁻¹ at hup
  obtain ⟨T,hTnorm,hT⟩ := canonical_inverse_data d (heightPoint (-2*ζ.re) η) (by simpa using hη)
  have hn := inverse_implies_nonzero_modes d ζ hζ _ T hT
  have hnβ : ∀k,0<‖beta d ζ (heightPoint (-2*ζ.re) η) k‖ := fun k => norm_pos_iff.mpr (hn k)
  have hinvupper : ∀k : Fin d,‖beta d ζ (heightPoint (-2*ζ.re) η) k‖⁻¹≤B/η := by
    intro k
    apply (le_div_iff₀ hη).mpr
    by_cases hk : k=singularIndex d hd
    · subst k
      have hx := (lt_div_iff₀ hη).mp hlo
      have hz := inv_mul_cancel₀ (hnβ (singularIndex d hd)).ne'
      have himul := mul_le_mul_of_nonneg_right hx.le
        (show 0≤2*ζ.im*‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖⁻¹ by positivity)
      have hiid : ζ.im⁻¹*ζ.im=1 := inv_mul_cancel₀ hi.ne'
      dsimp [B]
      nlinarith [inv_nonneg.mpr hc.le]
    · have hsep := hotherη k hk
      have hv := (inv_le_inv₀ (hnβ k) hc).mpr hsep
      have hmul := mul_le_mul_of_nonneg_left hη1 (inv_nonneg.mpr (norm_nonneg
        (beta d ζ (heightPoint (-2*ζ.re) η) k)))
      dsimp [B]
      nlinarith
  have hupper := inverse_fourier_upper d ζ hζ _ T hT (B/η) (by positivity) hn hinvupper
  have hlower := inverse_mode_lower d ζ hζ _ T hT (singularIndex d hd) (hn _)
  rw [hTnorm] at hupper hlower
  constructor
  · have hx := (div_lt_iff₀ hη).mp hup
    have hz := inv_mul_cancel₀ (hnβ (singularIndex d hd)).ne'
    have hmul := mul_le_mul_of_nonneg_right hx.le
      (show 0≤ζ.im*‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖⁻¹ by positivity)
    have hiid : ζ.im⁻¹*ζ.im=1 := inv_mul_cancel₀ hi.ne'
    apply (div_le_iff₀ hη).mpr
    have hh := mul_le_mul_of_nonneg_right hlower hη.le
    change ‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖⁻¹*η≤_ at hh
    nlinarith
  · convert hupper using 1 <;> ring

end NonSymmetricDyson.Paper.CyclicFourier
