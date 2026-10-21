import Dyson.Paper.SpectralPoint
import Dyson.Paper.SpectralBlockBounds
import Dyson.Paper.SpectralStable
import Dyson.Paper.SpectralNearbyLengths
import Dyson.Paper.PerronNormalizedFrame
import Dyson.Paper.PerronRestricted

/-! Revised local spectral lemma at an actual regular edge or cusp.
All model-specific premises and coefficients are verified. The universal
quantitative simple-eigenvalue theorem is the explicitly declared external
complex spectral argument, including its Rouché/Taylor remainder mechanism. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Spectral Full.Singularities Full.SingularSpectral Full.PerronContinuation ExternalAlgebraic

/-- Original-quantifier endpoint on a full closed upper neighborhood. The
same Euclidean-normalized frame, small eigenvalue and eigenvectors occur in
all clauses, including the new boundary convention and exact Schur/residual
identities. No Dyson-specific spectral conclusion is an input. -/
theorem edge_cusp_spectral_expansion {n : ℕ}
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (perron : ExternalContinuousPerron) (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ (p : Fin n → ℝ)
      (frame : VaryingFrame S (Boundary.boundaryVector m) (𝓝[closedUpper] (τ:ℂ))
        (Boundary.boundaryVector m (τ:ℂ))) (epsilon rho C CU b B : ℝ),
      (∀ j,p j^2=1) ∧ (∀ j,0<p j*(Boundary.boundaryVector m (τ:ℂ) j).re) ∧
      0<epsilon ∧ 0<rho ∧ 0<C ∧ 0<CU ∧ 0<b ∧ 0<B ∧
      (∑ j,frame.r₀ j^2=1) ∧
      Tendsto (fun z => extendedHeightRatio (frame.lam z) (frame.l z) (Boundary.boundaryVector m z))
        (𝓝[closedUpper] (τ:ℂ)) (𝓝 0) ∧
      ∀ z : ℂ,0≤z.im → ‖z-(τ:ℂ)‖≤epsilon →
        (∀ j,0<p j*(Boundary.boundaryVector m z j).re) ∧
        (∑ j,frame.r z j^2=1) ∧
        PerronData (saturatedMatrix S (Boundary.boundaryVector m z)) (frame.lam z) (frame.r z) (frame.l z) ∧
        Nonempty (ExpansionAt S (Boundary.boundaryVector m z) p (frame.r z) (frame.l z)
          (frame.K z) (frame.lam z) z.im rho C CU b B) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ := Boundary.boundaryVector m (τ:ℂ)
  have hreal := Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hnz := (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  let p : Fin n → ℝ := fun j => if (m₀ j).re<0 then -1 else 1
  have hp : ∀ j,p j^2=1 := by intro j; dsimp [p]; split_ifs <;> norm_num
  have hp0 : ∀ j,0<p j*(m₀ j).re := by
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
  obtain ⟨raw⟩ := regular_frontier_varying_frame perron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  obtain ⟨frame,_,_,_,_,hunit₀,hunit⟩ := Perron.normalized_varying_frame hn S _ _ _ raw
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  have hη : Tendsto (fun z : ℂ => z.im) (𝓝[closedUpper] (τ:ℂ)) (𝓝 0) := by
    simpa using Complex.continuous_im.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hactual := regular_closed_upper_equation algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨rho,C,hrho,hC,hnear⟩ := varying_spectral_expansion hn external S a
    (𝓝[closedUpper] (τ:ℂ)) id (Boundary.boundaryVector m) m₀ frame hm hη hreal hnz p hp hp0 hactual
  obtain ⟨CU,hCU,hphase⟩ := varying_phase_expansion hn S a
    (𝓝[closedUpper] (τ:ℂ)) id (Boundary.boundaryVector m) m₀ frame hm hη hreal hnz p hp hp0 hactual
  obtain ⟨b,B,hb,hB,hlengths⟩ := varying_spectral_lengths hn S _ _ _ frame hm
    (fun z : ℂ => z.im) hη hreal hnz p rho C
  have hsign : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),∀ j,0<p j*(Boundary.boundaryVector m z j).re := by
    apply Filter.eventually_all.mpr
    intro j
    exact PhaseTaylor.eventually_real_sign _ _ _ ((tendsto_pi_nhds.mp hm) j) (hp0 j)
  have hall : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      (∀ j,0<p j*(Boundary.boundaryVector m z j).re) ∧ (∑ j,frame.r z j^2=1) ∧
      PerronData (saturatedMatrix S (Boundary.boundaryVector m z)) (frame.lam z) (frame.r z) (frame.l z) ∧
      Nonempty (ExpansionAt S (Boundary.boundaryVector m z) p (frame.r z) (frame.l z)
        (frame.K z) (frame.lam z) z.im rho C CU b B) := by
    filter_upwards [hnear,hphase,hlengths,hsign,hunit,frame.nearby,frame.restricted,hactual]
      with z hz hpz hlz hsz hnz hd hK hactualz
    obtain ⟨u,d,hu,hest⟩ := hz
    obtain ⟨hrlen,hllen,hpair⟩ := hlz u d hest
    exact ⟨hsz,hnz,hd,expansionAt_of_estimates S _ p _ _ u _ _ _ rho C CU b B
      hactualz.1 hd hK hrho hC d hu hest hpz hrlen hllen hpair⟩
  obtain ⟨epsilon,hepsilon,hdisc⟩ := closed_upper_eventual_radius τ _ hall
  exact ⟨p,frame,epsilon,rho,C,CU,b,B,hp,hp0,hepsilon,hrho,hC,hCU,hb,hB,hunit₀,
    varying_frame_heightRatio_limit hn S _ _ _ frame hm hnz,hdisc⟩

end NonSymmetricDyson.Paper.Spectral
