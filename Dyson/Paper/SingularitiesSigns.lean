import Dyson.Paper.SingularitiesUniform
import Dyson.Full.PhaseTaylor

/-! The fixed boundary signs used by the analytic charts equal the paper's
moving signs sign(Re m(z)) throughout a genuine closed-upper neighborhood. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.SingularitiesSigns
open Full Full.Singularities Full.PerronContinuation

theorem sign_eq_of_square_one (p x : ℝ) (hp : p^2=1) (hx : 0<p*x) : Real.sign x=p := by
  rcases sq_eq_one_iff.mp hp with h|h
  · subst p
    exact Real.sign_of_pos (by simpa using hx)
  · subst p
    exact Real.sign_of_neg (by nlinarith)

/-- A finite nonzero real limiting vector has locally constant real signs. -/
theorem signs_near_real_limit {X ι : Type*} [Fintype ι] {L : Filter X}
    (m : X → ι → ℂ) (m₀ : ι → ℂ)
    (hm : Tendsto m L (𝓝 m₀)) (hreal : ∀ j,(m₀ j).im=0) (hnz : ∀ j,m₀ j≠0) :
    ∀ᶠ x in L,(fun j => Real.sign (m x j).re)=
      (fun j => (m₀ j).re/‖m₀ j‖) := by
  have hsign : ∀ j,∀ᶠ x in L,Real.sign (m x j).re=(m₀ j).re/‖m₀ j‖ := by
    intro j
    have hr : ((m₀ j).re:ℂ)=m₀ j := Complex.ext rfl (by simp [hreal])
    have hnorm : ‖m₀ j‖=|(m₀ j).re| := by
      calc
        ‖m₀ j‖=‖((m₀ j).re:ℂ)‖ := congrArg norm hr.symm
        _=|(m₀ j).re| := by simp
    have hp : ((m₀ j).re/‖m₀ j‖)^2=1 := by
      rw [hnorm,div_pow,sq_abs,div_self]
      exact pow_ne_zero 2 (by intro hz;apply hnz j;rw [← hr,hz];rfl)
    have hx : 0<((m₀ j).re/‖m₀ j‖)*(m₀ j).re := by
      rw [div_mul_eq_mul_div]
      apply div_pos
      · exact mul_self_pos.mpr (by intro hz;apply hnz j;rw [← hr,hz];rfl)
      · exact norm_pos_iff.mpr (hnz j)
    exact (PhaseTaylor.eventually_real_sign (fun x => m x j) (m₀ j) _
      ((tendsto_pi_nhds.mp hm) j) hx).mono fun x hx => sign_eq_of_square_one _ _ hp hx
  filter_upwards [eventually_all.mpr hsign] with x hx
  exact funext hx

/-- This is the actual solution and actual regular frontier, not an
independent sign-continuity premise. -/
theorem actual_frontier_signs {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
      (fun j => Real.sign (Boundary.boundaryVector m z j).re)=
        (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) := by
  exact signs_near_real_limit (Boundary.boundaryVector m) _
    (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
    (Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ)
    (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1

end NonSymmetricDyson.Paper.SingularitiesSigns
