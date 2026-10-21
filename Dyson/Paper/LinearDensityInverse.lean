import Dyson.Paper.LinearFrame
import Dyson.Paper.SingularitiesUniform
import Dyson.Paper.SingularitiesPrescribed

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearFrame
open Full Full.Singularities Full.SingularSpectral Full.Spectral Full.PerronContinuation
open Full.ExternalAlgebraic

def restrictFrame {X : Type*} {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    {m : X → Fin n → ℂ} {m₀ : Fin n → ℂ} {L L' : Filter X}
    (frame : VaryingFrame S m L m₀) (h : L'≤L) : VaryingFrame S m L' m₀ :=
  { frame with
    lam_limit := frame.lam_limit.mono_left h
    right_limit := frame.right_limit.mono_left h
    left_limit := frame.left_limit.mono_left h
    nearby := frame.nearby.filter_mono h
    restricted := frame.restricted.filter_mono h
    real_preserving := frame.real_preserving.filter_mono h
    uniform := by
      obtain ⟨B,b,hB,hb,hbounds⟩ := frame.uniform
      exact ⟨B,b,hB,hb,hbounds.filter_mono h⟩ }

theorem density_inverse_with_frame {n : ℕ} (hn : 0<n)
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀z∈upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀z∈upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ∉Boundary.singularUnion m)
    (frame : VaryingFrame S (Boundary.boundaryVector m) (𝓝[closedUpper] (τ:ℂ))
      (Boundary.boundaryVector m (τ:ℂ)))
    (D : FrontierData S (Boundary.boundaryVector m (τ:ℂ)))
    (b : ℝ) (hb : 0<b)
    (hnd : ∀ᶠ z in 𝓝[closedUpper] (τ:ℂ),
      b≤(quadraticCoefficient D.p (frame.l z) (frame.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) D.p (frame.l z) (frame.r z)
        (stableCoefficient D.p (frame.r z) (frame.K z))) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        C/(∑i,(m z i).im)^2 := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hfilter : 𝓝[upper] (τ:ℂ)≤𝓝[closedUpper] (τ:ℂ) :=
    nhdsWithin_mono _ (fun z hz => show 0≤z.im from le_of_lt hz)
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  have hp0 : ∀i,0<D.p i*(Boundary.boundaryVector m (τ:ℂ) i).re := by
    intro i
    rw [←D.norm_sign]
    exact norm_pos_iff.mpr (D.nonzero i)
  have hactual : ∀ᶠ z in 𝓝[upper] (τ:ℂ),0<z.im ∧
      BasicEstimates.IsUpperSolution (Boundary.boundaryVector m z) ∧
      BasicEstimates.IsDysonSolution S a z (Boundary.boundaryVector m z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [Boundary.family_extension_agrees S a hS m hupper heq z hz]
    exact ⟨hz,hupper z hz,heq z hz⟩
  have hη : Tendsto (fun z : ℂ => z.im) (𝓝[upper] (τ:ℂ)) (𝓝 0) := by
    simpa using Complex.continuous_im.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨C,hC,hbound⟩ := inverse_from_frame external hn S a hS (𝓝[upper] (τ:ℂ)) id
    (Boundary.boundaryVector m) _ (restrictFrame frame hfilter) (hm.mono_left hfilter) hη
    D.real_value D.nonzero D.p D.sign_square hp0 hactual b hb (hnd.filter_mono hfilter)
  obtain ⟨c,C',hc,hC',hcompare⟩ := frame.density_comparison hm D.nonzero
  refine ⟨C/c^2,by positivity,?_⟩
  filter_upwards [hbound,hcompare.filter_mono hfilter,self_mem_nhdsWithin] with z hzbound hzcompare hz
  intro hz'
  have hext := Boundary.family_extension_agrees S a hS m hupper heq z hz
  have hbnd := hzbound hz (by rw [hext]; exact hupper z hz) (by rw [hext]; exact heq z hz)
  change ‖EuclideanInverse.stabilityInverse S a z (Boundary.boundaryVector m z) hS hz _ _‖≤
    C/(perronDensity (frame.l z) (Boundary.boundaryVector m z))^2 at hbnd
  simp only [hext] at hbnd
  have hcmp := hzcompare (fun i => by rw [hext]; exact (hupper z hz i).le)
  rw [hext] at hcmp
  have hρ : 0<∑i,(m z i).im := Finset.sum_pos (fun i _ => hupper z hz i) Finset.univ_nonempty
  have hδ : 0<perronDensity (frame.l z) (m z) := (mul_pos hc hρ).trans_le hcmp.1
  have hsq := (sq_le_sq₀ (by positivity) hδ.le).mpr hcmp.1
  have hdiv : C/(perronDensity (frame.l z) (m z))^2≤(C/c^2)/(∑i,(m z i).im)^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hδ) (sq_pos_of_pos hρ)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  exact hbnd.trans hdiv

/-- Original β→inverse proof for the actual symmetric Dyson model. -/
theorem symmetric_density_inverse {n : ℕ} (hn : 0<n)
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (perron : ExternalContinuousPerron)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (hsym : ∀i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀z∈upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀z∈upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        C/(∑j,(m z j).im)^2 := by
  obtain ⟨frame⟩ := regular_frontier_varying_frame perron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  obtain ⟨D,hp,hr,hl⟩ := SingularitiesFrontier.data_with_perron_symmetric hn algebraic puiseux
    S a hS hirr hsym m hupper heq τ i hfront hτ frame.r₀ frame.l₀ frame.center
  obtain ⟨b,B,hb,hB,hnd⟩ := SingularitiesUniform.uniform_nondegeneracy_symmetric hn algebraic puiseux
    S a hS hirr hsym m hupper heq τ i hfront hτ frame
  apply density_inverse_with_frame hn external algebraic puiseux S a hS m hupper heq τ hτ frame D b hb
  simpa only [hp] using hnd.mono (fun _ h => h.1)

theorem nonbacktracking_density_inverse {n : ℕ} (hn : 0<n)
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (perron : ExternalContinuousPerron)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀i j,S i j=G.matrix (e i) (e j))
    (hpot : ∀i,a i=av (G.head (e i)))
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀z∈upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀z∈upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        C/(∑j,(m z j).im)^2 := by
  obtain ⟨frame⟩ := regular_frontier_varying_frame perron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  obtain ⟨D,hp,hr,hl⟩ := SingularitiesFrontier.data_with_perron_nonbacktracking hn algebraic puiseux
    S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ frame.r₀ frame.l₀ frame.center
  obtain ⟨b,B,hb,hB,hnd⟩ := SingularitiesUniform.uniform_nondegeneracy_nonbacktracking hn algebraic puiseux
    S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ frame
  apply density_inverse_with_frame hn external algebraic puiseux S a hS m hupper heq τ hτ frame D b hb
  simpa only [hp] using hnd.mono (fun _ h => h.1)

end NonSymmetricDyson.Paper.LinearFrame
