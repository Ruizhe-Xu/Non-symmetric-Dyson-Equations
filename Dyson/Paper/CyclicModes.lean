import Dyson.Paper.CyclicFourierInverse
import Dyson.Full.CyclicSemicircle

noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full.CyclicGeneral Full.CyclicExample
variable (d : ℕ) [NeZero d]

def beta (ζ z : ℂ) (k : Fin d) : ℂ := 1-(scalar z)^2*ζ^k.val

theorem beta_limit (ζ : ℂ) (hζ : ‖ζ‖=1) (hi : 0<ζ.im) (k : Fin d) :
    Tendsto (fun η => beta d ζ (heightPoint (-2*ζ.re) η) k)
      (𝓝[>] (0:ℝ)) (𝓝 (1-ζ^2*ζ^k.val)) := by
  have ht := (scalar_hasDerivAt_unit_energy ζ hζ hi).continuousAt.tendsto.comp
    (heightPoint_tendsto (-2*ζ.re))
  rw [scalar_at_unit_energy ζ hζ hi] at ht
  exact (tendsto_const_nhds (x := (1:ℂ))).sub ((ht.pow 2).mul_const (ζ^k.val))

theorem singular_beta_derivative (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (hi : 0<ζ.im) (hd : 3≤d) :
    HasDerivAt (fun z => beta d ζ z (singularIndex d hd))
      (((ζ.im:ℂ)*Complex.I)⁻¹) ((-2*ζ.re:ℝ):ℂ) := by
  have hn := hζ.norm'_eq_one (NeZero.ne d)
  have hh := (hasDerivAt_const (((-2*ζ.re:ℝ):ℂ)) (1:ℂ)).sub
    (((scalar_hasDerivAt_unit_energy ζ hn hi).pow 2).mul_const (ζ^(singularIndex d hd).val))
  have hden : (ζ.im:ℂ)*Complex.I≠0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hi.ne') Complex.I_ne_zero
  convert hh using 1
  rw [scalar_at_unit_energy ζ hn hi]
  have hp := singular_mode_power d ζ hζ hd
  have him : (ζ.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hi.ne'
  norm_num
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  linear_combination hp

theorem singular_beta_height_limit (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (hi : 0<ζ.im) (hd : 3≤d) :
    Tendsto (fun η : ℝ => ‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)‖/η)
      (𝓝[>] (0:ℝ)) (𝓝 (ζ.im⁻¹)) := by
  have hp : Tendsto (heightPoint (-2*ζ.re)) (𝓝[>] (0:ℝ))
      (𝓝[≠] (((-2*ζ.re:ℝ):ℂ))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨heightPoint_tendsto _,?_⟩
    filter_upwards [self_mem_nhdsWithin] with η hη
    intro he
    have hh := congrArg Complex.im he
    simpa using (ne_of_gt hη) (by simpa using hh)
  have hz : beta d ζ (((-2*ζ.re:ℝ):ℂ)) (singularIndex d hd)=0 := by
    rw [beta,scalar_at_unit_energy ζ (hζ.norm'_eq_one (NeZero.ne d)) hi,
      singular_mode_power d ζ hζ hd,sub_self]
  have hs := ((hasDerivAt_iff_tendsto_slope.mp (singular_beta_derivative d ζ hζ hi hd)).comp hp).norm
  have hn : ‖((ζ.im:ℂ)*Complex.I)⁻¹‖=ζ.im⁻¹ := by
    simp [norm_inv,norm_mul,Complex.norm_real,abs_of_pos hi]
  rw [hn] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  simp only [Function.comp_apply,slope,hz,vsub_eq_sub,sub_zero,smul_eq_mul,
    norm_mul,norm_inv,heightPoint_distance _ _ hη.le]
  ring

/-- All other Fourier eigenvalues remain uniformly separated from zero.
The quantifier over modes is inside the same neighborhood of η=0. -/
theorem nonsingular_modes_separated (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (hi : 0<ζ.im) (hd : 3≤d) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ η in 𝓝[>] (0:ℝ),
      ∀ k : Fin d,k≠singularIndex d hd →
        c≤‖beta d ζ (heightPoint (-2*ζ.re) η) k‖ := by
  classical
  have hlocal (k : Fin d) : ∃ c : ℝ,0<c ∧ ∀ᶠ η in 𝓝[>] (0:ℝ),
      k≠singularIndex d hd → c≤‖beta d ζ (heightPoint (-2*ζ.re) η) k‖ := by
    by_cases hk : k=singularIndex d hd
    · exact ⟨1,by norm_num,Eventually.of_forall (fun _ h => (h hk).elim)⟩
    · have hn : 0<‖1-ζ^2*ζ^k.val‖ := norm_pos_iff.mpr
        (fun h => hk ((unique_singular_mode d ζ hζ hd k).mp h))
      refine ⟨‖1-ζ^2*ζ^k.val‖/2,half_pos hn,?_⟩
      have he := ((beta_limit d ζ (hζ.norm'_eq_one (NeZero.ne d)) hi k).norm).eventually
        (lt_mem_nhds (show ‖1-ζ^2*ζ^k.val‖/2<‖1-ζ^2*ζ^k.val‖ by linarith))
      exact he.mono fun _ h _ => h.le
  choose c hc he using hlocal
  let c₀ := Finset.univ.inf' Finset.univ_nonempty c
  refine ⟨c₀,(Finset.lt_inf'_iff _).mpr (fun k _ => hc k),?_⟩
  filter_upwards [eventually_all.mpr he] with η hη k hk
  exact (Finset.inf'_le _ (Finset.mem_univ k)).trans (hη k hk)

end NonSymmetricDyson.Paper.CyclicFourier
