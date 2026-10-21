import Dyson.Full.ClassicalFrobenius
import Dyson.Full.PerronIdentity
import Dyson.Full.PerronContinuation
import Dyson.Full.BoundaryLocalLimits

noncomputable section
open scoped BigOperators Topology
open Filter
namespace NonSymmetricDyson.Full.Singularities

/-- A positive left/right pairing identifies any two positive Perron
values. No irreducibility or spectral-radius statement is assumed here. -/
theorem positive_perron_value_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Matrix ι ι ℝ) (l r : ι → ℝ) (lam rho : ℝ)
    (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (hlF : ∀ j, ∑ i, l i * F i j = lam * l j)
    (hFr : ∀ i, ∑ j, F i j * r j = rho * r i) : lam = rho := by
  have hp : 0 < ∑ i, l i * r i := Finset.sum_pos
    (fun i _ => mul_pos (hl i) (hr i)) Finset.univ_nonempty
  have he : lam * (∑ i, l i * r i) = rho * (∑ i, l i * r i) := by
    calc
      _ = ∑ j, (∑ i, l i * F i j) * r j := by simp_rw [hlF]; rw [Finset.mul_sum]; ring
      _ = ∑ i, l i * (∑ j, F i j * r j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp_rw [hFr]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
  exact mul_right_cancel₀ hp.ne' he

/-- The Perron value used in the actual Dyson calculations is the genuine
spectral radius: it is the greatest modulus of an actual characteristic root.
Peripheral roots are algebraically simple, as in the cited classical theorem. -/
theorem saturated_perron_spectrum
    (external : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : Fin n → ℂ) (hm : ∀ i, m i ≠ 0) (l : Fin n → ℝ) (lam : ℝ)
    (hl : ∀ i, 0 < l i)
    (hlF : ∀ j, ∑ i, l i * saturatedMatrix S m i j = lam * l j) :
    0 < lam ∧
    IsGreatest {t : ℝ | ∃ z : ℂ,
      ((saturatedMatrix S m).map Complex.ofRealHom).charpoly.IsRoot z ∧ ‖z‖ = t} lam ∧
    (∀ z : ℂ, ((saturatedMatrix S m).map Complex.ofRealHom).charpoly.IsRoot z → ‖z‖ = lam →
      ((saturatedMatrix S m).map Complex.ofRealHom).charpoly.derivative.eval z ≠ 0) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hF := saturatedMatrix_nonnegative S hS m
  have hi := saturatedMatrix_irreducible S hS hirr m hm
  obtain ⟨rho, hrho, L, R, hL, hR, hFR, _, hroot, hdom, hsimple⟩ :=
    external.spectral n hn (saturatedMatrix S m) hF hi
  have heq := positive_perron_value_unique (saturatedMatrix S m) l R lam rho hl hR hlF hFR
  subst rho
  refine ⟨hrho, ⟨?_, ?_⟩, hsimple⟩
  · exact ⟨(lam : ℂ), hroot, by simp [Complex.norm_real, abs_of_pos hrho]⟩
  · rintro t ⟨z, hz, rfl⟩
    exact hdom z hz

/-- Continuity transfers the upper-half-plane Perron bound to every real
regular boundary point. This generic limit step does not require positivity
of the boundary density. -/
theorem real_boundary_perron_le_one (lam : ℂ → ℝ) (τ : ℝ)
    (hc : ContinuousWithinAt lam ExternalAlgebraic.closedUpper (τ : ℂ))
    (hupper : ∀ᶠ z in 𝓝[ExternalAlgebraic.upper] (τ : ℂ), lam z ≤ 1) :
    lam (τ : ℂ) ≤ 1 := by
  letI : NeBot (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (Boundary.real_mem_closure_upper τ)
  have ht : Tendsto lam (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 (lam (τ : ℂ))) := (hc.mono (show ExternalAlgebraic.upper ⊆ ExternalAlgebraic.closedUpper
    from fun z hz => (show 0 < z.im from hz).le)).tendsto
  exact le_of_tendsto ht hupper

/-- The actual saturated Perron value is at most one at every finite regular
real boundary point, including points in spectral gaps. The argument uses the
generic local continuous Perron chart and the already proved strict interior
imaginary-part identity. -/
theorem regular_boundary_perron_le_one
    (external : PerronContinuation.ExternalContinuousPerron)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m) (l : Fin n → ℝ) (lam : ℝ)
    (hl : ∀ i, 0 < l i)
    (hlF : ∀ j, ∑ i, l i * saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)) i j = lam * l j) :
    lam ≤ 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : NeBot (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (Boundary.real_mem_closure_upper τ)
  let m₀ := Boundary.boundaryVector m (τ : ℂ)
  let F₀ := saturatedMatrix S m₀
  have hbe := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨U, hU, hFU, rho, R, L, hrho, hR, hL, hdata⟩ := external n hn F₀
    (saturatedMatrix_nonnegative S hS m₀) (saturatedMatrix_irreducible S hS hirr m₀ hbe.1)
  have hd := hdata F₀ hFU
  have heigen : lam = rho F₀ := positive_perron_value_unique F₀ l (R F₀) lam (rho F₀)
    hl hd.right_positive hlF hd.right_eigen
  have hlim : Tendsto m (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 m₀) := by
    have hb := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      (τ : ℂ) (Or.inr ⟨τ, hτ, rfl⟩)
    have ht := (hb.mono (show ExternalAlgebraic.upper ⊆ Boundary.commonRegularDomain m
      from fun _ hz => Or.inl hz)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S a hS m hupper heq z hz
  have hFlim : Tendsto (fun z => saturatedMatrix S (m z))
      (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) (𝓝 F₀) :=
    (PerronContinuation.saturatedMatrix_continuousAt S id m₀ continuousAt_id).tendsto.comp hlim
  have hrlim := (hrho.continuousAt (hU.mem_nhds hFU)).tendsto.comp hFlim
  rw [heigen]
  apply le_of_tendsto hrlim
  filter_upwards [hFlim.eventually (hU.mem_nhds hFU), self_mem_nhdsWithin] with z hz hzi
  have hzdata := hdata _ hz
  exact (perron_eigenvalue_lt_one S a z (m z) hzi (hupper z hzi) (heq z hzi)
    (L (saturatedMatrix S (m z))) (rho (saturatedMatrix S (m z)))
    hzdata.left_positive hzdata.left_eigen).le

end NonSymmetricDyson.Full.Singularities
