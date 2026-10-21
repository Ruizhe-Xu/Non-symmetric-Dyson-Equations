import Dyson.Paper.LinearEdgeFrame
import Dyson.Paper.LinearDensityInverse
import Dyson.Full.SingularityTopology

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearFrame
open Full Full.Singularities Full.SingularSpectral Full.Spectral Full.PerronContinuation
open Full.ExternalAlgebraic

theorem edge_inverse_with_frame {n : ℕ} (hn : 0<n)
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀z∈upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀z∈upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) (hedge : IsRegularEdge (Boundary.regularSupport m i) τ)
    (frame : VaryingFrame S (Boundary.boundaryVector m) (𝓝[closedUpper] (τ:ℂ))
      (Boundary.boundaryVector m (τ:ℂ)))
    (D : FrontierData S (Boundary.boundaryVector m (τ:ℂ)))
    (hr : D.r=frame.r₀) (hl : D.l=frame.l₀)
    (B : ℝ) (hB : 0<B)
    (hnd : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      (quadraticCoefficient D.p (frame.l z) (frame.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) D.p (frame.l z) (frame.r z)
        (stableCoefficient D.p (frame.r z) (frame.K z))≤B) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      c/((1-frame.lam z)+perronDensity (frame.l z) (m z))≤
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        C/((1-frame.lam z)+perronDensity (frame.l z) (m z)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  have hfilter : 𝓝[upper] (τ:ℂ)≤𝓝[closedUpper] (τ:ℂ) :=
    nhdsWithin_mono _ (fun z hz => show 0≤z.im from le_of_lt hz)
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  have hp0 : ∀j,0<D.p j*(Boundary.boundaryVector m (τ:ℂ) j).re := by
    intro j
    rw [←D.norm_sign]
    exact norm_pos_iff.mpr (D.nonzero j)
  have hσ0 : quadraticCoefficient D.p frame.l₀ frame.r₀≠0 := by
    rw [←hr,←hl]
    exact (frontier_coefficient_iff_support_topology normalForm orientation hn algebraic puiseux
      S a hS hirr m hupper heq τ i hfront hτ D).1.mpr hedge
  let s := |quadraticCoefficient D.p frame.l₀ frame.r₀|/2
  let M := |quadraticCoefficient D.p frame.l₀ frame.r₀|+1
  have hs : 0<s := half_pos (abs_pos.mpr hσ0)
  have hM : 0<M := by dsimp [M]; positivity
  have hσlim := (quadratic_tendsto (𝓝[closedUpper] (τ:ℂ)) D.p frame.l frame.r
    frame.l₀ frame.r₀ frame.left_limit frame.right_limit).abs
  have hσlo := hσlim.eventually_const_le
    (show s < |quadraticCoefficient D.p frame.l₀ frame.r₀| by dsimp [s]; linarith [abs_pos.mpr hσ0])
  have hσhi := hσlim.eventually_le_const
    (show |quadraticCoefficient D.p frame.l₀ frame.r₀|<M by dsimp [M]; linarith)
  have hactual : ∀ᶠ z in 𝓝[upper] (τ:ℂ),0<z.im ∧
      BasicEstimates.IsUpperSolution (Boundary.boundaryVector m z) ∧
      BasicEstimates.IsDysonSolution S a z (Boundary.boundaryVector m z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Boundary.family_extension_agrees S a hS m hupper heq z hz]
    exact ⟨hz,hupper z hz,heq z hz⟩
  have hcoeff : ∀ᶠ z in 𝓝[upper] (τ:ℂ),
      s≤|quadraticCoefficient D.p (frame.l z) (frame.r z)| ∧
      |quadraticCoefficient D.p (frame.l z) (frame.r z)|≤M ∧
      |cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) D.p (frame.l z) (frame.r z)
        (stableCoefficient D.p (frame.r z) (frame.K z))-
          (quadraticCoefficient D.p (frame.l z) (frame.r z))^2|≤B := by
    filter_upwards [hσlo.filter_mono hfilter,hσhi.filter_mono hfilter,hnd.filter_mono hfilter,
      frame.nearby.filter_mono hfilter,frame.restricted.filter_mono hfilter,hactual]
      with z hlo hhi hndz hf hK hz
    have hψ := actual_cubic_positive_upper S a z (Boundary.boundaryVector m z) hS hz.1 hz.2.1 hz.2.2
      D.p (frame.r z) (frame.l z) (frame.lam z) hf (frame.K z) hK
    refine ⟨hlo,hhi,abs_le.mpr ⟨?_,?_⟩⟩ <;>
      nlinarith [sq_nonneg (quadraticCoefficient D.p (frame.l z) (frame.r z))]
  have hη : Tendsto (fun z : ℂ => z.im) (𝓝[upper] (τ:ℂ)) (𝓝 0) := by
    simpa using Complex.continuous_im.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨c,C,hc,hC,hbound⟩ := edge_inverse_from_frame external hn S a hS (𝓝[upper] (τ:ℂ)) id
    (Boundary.boundaryVector m) _ (restrictFrame frame hfilter) (hm.mono_left hfilter) hη
    D.real_value D.nonzero D.p D.sign_square hp0 hactual s M B hs hM.le hB.le hcoeff
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound,self_mem_nhdsWithin] with z hzbound hz
  intro hz'
  have hext := Boundary.family_extension_agrees S a hS m hupper heq z hz
  have hbnd := hzbound hz (by rw [hext]; exact hupper z hz) (by rw [hext]; exact heq z hz)
  simpa only [restrictFrame,hext,id_eq] using hbnd

end NonSymmetricDyson.Paper.LinearFrame
