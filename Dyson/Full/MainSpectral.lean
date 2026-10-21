import Dyson.Full.SpectralNearby

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities Spectral PerronContinuation ExternalAlgebraic

/-- The canonical closed boundary extension satisfies the original Dyson
equation and has nonnegative imaginary coordinates on a full closed upper
neighborhood of each regular real point. -/
theorem regular_closed_upper_equation {n : ℕ}
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S) (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m) :
    ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      (∀ i, Boundary.boundaryVector m z i≠0) ∧
      BasicEstimates.IsDysonSolution S a z (Boundary.boundaryVector m z) ∧
      (∀ i, 0≤normalizedImag (Boundary.boundaryVector m z) i) ∧ 0≤z.im := by
  have hopen := (Boundary.family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
  have hreg : ∀ᶠ z : ℂ in 𝓝 (τ:ℂ), z.re∉Boundary.singularUnion m :=
    Complex.continuous_re.continuousAt.tendsto.eventually
      (hopen.mem_nhds (show (τ:ℂ).re∈(Boundary.singularUnion m)ᶜ from hτ))
  filter_upwards [self_mem_nhdsWithin,hreg.filter_mono nhdsWithin_le_nhds] with z hz hr
  change 0≤z.im at hz
  by_cases hi : 0<z.im
  · have hv := Boundary.family_extension_agrees S a hS m hupper heq z hi
    rw [hv]
    refine ⟨fun i h => ?_,heq z hi,fun i => div_nonneg (hupper z hi i).le (norm_nonneg _),hz⟩
    simpa [h] using hupper z hi i
  · have hi0 : z.im=0 := le_antisymm (le_of_not_gt hi) hz
    have he : (z.re:ℂ)=z := by apply Complex.ext <;> simp [hi0]
    have hd := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq z.re hr
    rw [he] at hd
    exact ⟨hd.1,hd.2.2,fun i => div_nonneg (hd.2.1 i) (norm_nonneg _),hz⟩

theorem closed_upper_eventual_radius (τ : ℝ) (P : ℂ → Prop)
    (h : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ), P z) :
    ∃ ε : ℝ, 0<ε ∧ ∀ z : ℂ, 0≤z.im → ‖z-(τ:ℂ)‖≤ε → P z := by
  obtain ⟨U,hU,hUP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ε/2,half_pos hε,?_⟩
  intro z hz hd
  apply hUP
  refine ⟨hball ?_,hz⟩
  change dist z (τ:ℂ)<ε
  rw [dist_eq_norm]
  linarith

/-- The complete nearby varying spectral expansion at an actual regular
support frontier. The neighborhood includes its real gap/support sides and
the singular center. The small eigenvalue and spectral data are outputs.
Only standard general algebraicity, Puiseux and finite-matrix Perron/spectral
perturbation theorems are external inputs. -/
theorem regular_frontier_spectral_expansion {n : ℕ}
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (perron : ExternalContinuousPerron) (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ (p : Fin n → ℝ)
      (frame : VaryingFrame S (Boundary.boundaryVector m) (𝓝[closedUpper] (τ:ℂ))
        (Boundary.boundaryVector m (τ:ℂ))) (ε ρ C CU : ℝ),
      (∀ j, p j^2=1) ∧ (∀ j, 0<p j*(Boundary.boundaryVector m (τ:ℂ) j).re) ∧
      0<ε ∧ 0<ρ ∧ 0<C ∧ 0<CU ∧
      ∀ z : ℂ, 0≤z.im → ‖z-(τ:ℂ)‖≤ε →
        ∃ (u : Fin n → ℝ) (d : SimpleSpectralSplit (reducedOperator S (Boundary.boundaryVector m z))),
          frame.K z (fun j => (p j:ℂ)*(frame.r z j:ℂ)^2)=(fun j => (u j:ℂ)) ∧
          HasDysonSpectralEstimates S (Boundary.boundaryVector m z) p (frame.r z) (frame.l z) u
            (frame.K z) (frame.lam z) (perronDensity (frame.l z) (Boundary.boundaryVector m z))
            z.im ρ C d ∧
          ‖phaseOperator (Boundary.boundaryVector m z)-ContinuousLinearMap.id ℂ (Vec (Fin n)) -
            (perronDensity (frame.l z) (Boundary.boundaryVector m z):ℂ) • firstPhase p (frame.r z) -
            ((perronDensity (frame.l z) (Boundary.boundaryVector m z):ℂ)^2) • secondPhase (frame.r z)‖ ≤
          CU*((perronDensity (frame.l z) (Boundary.boundaryVector m z))^3+z.im) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ := Boundary.boundaryVector m (τ:ℂ)
  have hreal := Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hnz := (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  let p : Fin n → ℝ := fun j => if (m₀ j).re<0 then -1 else 1
  have hp : ∀ j, p j^2=1 := by intro j; dsimp [p]; split_ifs <;> norm_num
  have hp0 : ∀ j, 0<p j*(m₀ j).re := by
    intro j
    have hrne : (m₀ j).re≠0 := by
      intro h
      apply hnz j
      apply Complex.ext
      · simpa using h
      · simpa using hreal j
    dsimp [p]
    split_ifs with h
    · linarith
    · have hh : 0<(m₀ j).re := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hrne)
      simpa using hh
  obtain ⟨frame⟩ := regular_frontier_varying_frame perron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  have hη : Tendsto (fun z : ℂ => z.im) (𝓝[closedUpper] (τ:ℂ)) (𝓝 0) := by
    simpa using Complex.continuous_im.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨ρ,C,hρ,hC,hnear⟩ := varying_spectral_expansion hn external S a
    (𝓝[closedUpper] (τ:ℂ)) id (Boundary.boundaryVector m) m₀ frame hm hη hreal hnz p hp hp0
    (regular_closed_upper_equation algebraic puiseux S a hS m hupper heq τ hτ)
  obtain ⟨CU,hCU,hphase⟩ := varying_phase_expansion hn S a
    (𝓝[closedUpper] (τ:ℂ)) id (Boundary.boundaryVector m) m₀ frame hm hη hreal hnz p hp hp0
    (regular_closed_upper_equation algebraic puiseux S a hS m hupper heq τ hτ)
  have hboth : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      ∃ (u : Fin n → ℝ) (d : SimpleSpectralSplit (reducedOperator S (Boundary.boundaryVector m z))),
        frame.K z (fun j => (p j:ℂ)*(frame.r z j:ℂ)^2)=(fun j => (u j:ℂ)) ∧
        HasDysonSpectralEstimates S (Boundary.boundaryVector m z) p (frame.r z) (frame.l z) u
          (frame.K z) (frame.lam z) (perronDensity (frame.l z) (Boundary.boundaryVector m z)) z.im ρ C d ∧
        ‖phaseOperator (Boundary.boundaryVector m z)-ContinuousLinearMap.id ℂ (Vec (Fin n)) -
          (perronDensity (frame.l z) (Boundary.boundaryVector m z):ℂ) • firstPhase p (frame.r z) -
          ((perronDensity (frame.l z) (Boundary.boundaryVector m z):ℂ)^2) • secondPhase (frame.r z)‖ ≤
        CU*((perronDensity (frame.l z) (Boundary.boundaryVector m z))^3+z.im) := by
    filter_upwards [hnear,hphase] with z hz hpz
    obtain ⟨u,d,hKu,hd⟩ := hz
    exact ⟨u,d,hKu,hd,hpz⟩
  obtain ⟨ε,hε,hdisc⟩ := closed_upper_eventual_radius τ _ hboth
  exact ⟨p,frame,ε,ρ,C,CU,hp,hp0,hε,hρ,hC,hCU,hdisc⟩

end NonSymmetricDyson.Full.SingularSpectral
