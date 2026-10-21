import Dyson.Paper.Cyclic
import Dyson.Paper.CyclicAlgebra

noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full Full.CyclicGeneral Full.CyclicExample
variable (d : ℕ) [NeZero d]

theorem omega_eq_cyclicOmega : omega d=cyclicOmega d := by
  unfold omega cyclicOmega
  congr 1
  push_cast
  ring

/-- The manuscript's δ expansion, with an actual uniform O(η²) bound. -/
theorem relative_solution_taylor (ζ : ℂ) (hζ : ‖ζ‖=1) (hi : 0<ζ.im) :
    ∃ C r : ℝ,0<C ∧ 0<r ∧ ∀η : ℝ,0<η → η<r →
      ‖scalar (heightPoint (-2*ζ.re) η)/ζ-1+(η:ℂ)/(2*ζ.im:ℂ)‖≤C*η^2 := by
  exact relative_taylor_algebraic ζ hζ hi

theorem quadratic_mode_remainder (δ : ℂ) {η a C : ℝ}
    (hη : 0≤η) (ha : 0≤a) (hC : 0≤C) (hη1 : η≤1)
    (he : ‖δ+(a*η:ℝ)‖≤C*η^2) :
    ‖1-(1+δ)^2-(2*a*η:ℝ)‖≤(2*C+(C+a)^2)*η^2 := by
  have hd : ‖δ‖≤(C+a)*η := by
    have ht : ‖δ‖≤‖δ+(a*η:ℝ)‖+a*η := by
      simpa [norm_neg,Complex.norm_real,abs_of_nonneg ha,abs_of_nonneg hη] using
        norm_sub_le (δ+(a*η:ℝ)) ((a*η:ℝ):ℂ)
    have hh := mul_le_mul_of_nonneg_left hη1 (show 0≤C*η by positivity)
    nlinarith
  have hid : 1-(1+δ)^2-(2*a*η:ℝ)= -2*(δ+(a*η:ℝ))-δ^2 := by push_cast; ring
  rw [hid]
  calc
    _ ≤ ‖-2*(δ+(a*η:ℝ))‖+‖δ^2‖ := norm_sub_le _ _
    _ = 2*‖δ+(a*η:ℝ)‖+‖δ‖^2 := by simp
    _ ≤ 2*(C*η^2)+((C+a)*η)^2 := by
      nlinarith [sq_le_sq₀ (norm_nonneg δ) (by positivity : 0≤(C+a)*η) |>.mpr hd]
    _ = _ := by ring

/-- The unique singular Fourier eigenvalue has the literal second-order
remainder from the appendix, not only a first-order limit. -/
theorem singular_beta_taylor (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    (hi : 0<ζ.im) (hd : 3≤d) :
    ∃ C r : ℝ,0<C ∧ 0<r ∧ ∀η : ℝ,0<η → η<r →
      ‖beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)-(η/ζ.im:ℝ)‖≤C*η^2 := by
  obtain ⟨C,r,hC,hr,ht⟩ := relative_solution_taylor ζ (hζ.norm'_eq_one (NeZero.ne d)) hi
  let a : ℝ := (2*ζ.im)⁻¹
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨2*C+(C+a)^2,min r 1,by positivity,lt_min hr (by norm_num),?_⟩
  intro η hη hηr
  let δ : ℂ := scalar (heightPoint (-2*ζ.re) η)/ζ-1
  have herr : ‖δ+(a*η:ℝ)‖≤C*η^2 := by
    convert ht η hη (lt_of_lt_of_le hηr (min_le_left r 1)) using 1
    congr 1
    dsimp [δ,a]
    push_cast
    ring
  have hb := quadratic_mode_remainder δ hη.le ha.le hC.le
    (le_of_lt (lt_of_lt_of_le hηr (min_le_right r 1))) herr
  have hn : ζ^2≠0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne d))
  have hp : ζ^(singularIndex d hd).val=(ζ^2)⁻¹ := by
    apply mul_left_cancel₀ hn
    rw [singular_mode_power d ζ hζ hd,mul_inv_cancel₀ hn]
  have heq : beta d ζ (heightPoint (-2*ζ.re) η) (singularIndex d hd)=1-(1+δ)^2 := by
    rw [beta,hp,←div_eq_mul_inv,←div_pow]
    dsimp [δ]
    ring
  rw [heq]
  convert hb using 1
  congr 1
  dsimp [a]
  push_cast
  field_simp

/-- Final appendix endpoint at precisely −2 cos(2π/d), with no stronger
claim about unrelated resonant energies. Its proof uses the Fourier basis. -/
theorem appendix_counterexample (hd : 3≤d) :
    -2 < -2*Real.cos (2*Real.pi/(d:ℝ)) ∧ -2*Real.cos (2*Real.pi/(d:ℝ)) < 2 ∧
    ∃ c C r : ℝ,0<c ∧ 0<C ∧ 0<r ∧ ∀η : ℝ,∀hη : 0<η,η<r →
      c/η≤canonicalInverseNorm d (heightPoint (-2*Real.cos (2*Real.pi/(d:ℝ))) η) (by simpa using hη) ∧
      canonicalInverseNorm d (heightPoint (-2*Real.cos (2*Real.pi/(d:ℝ))) η) (by simpa using hη)≤C/η := by
  have hu := cyclicOmega_upper d hd
  have he := unit_upper_energy (cyclicOmega d) (cyclicOmega_norm d) hu
  have hb := canonical_inverse_order_fourier d (omega d) (omega_primitive d)
    (by simpa only [omega_eq_cyclicOmega] using hu) hd
  rw [omega_eq_cyclicOmega] at hb
  simpa only [cyclicOmega_re] using And.intro he.1 (And.intro he.2 hb)

/-- Actual canonical cycle solution and its semicircle measure, used at the
start of the appendix before choosing the resonant interior energy. -/
alias canonical_scalar := Full.CyclicGeneral.canonical_eq_scalar_global
alias semicircle_density := Full.CyclicGeneral.canonical_boundary_imaginary
alias bulk_interval := Full.CyclicGeneral.regularSupport_eq
alias semicircle_measure := Full.CyclicGeneral.canonical_semicircle_measure

end NonSymmetricDyson.Paper.CyclicFourier
