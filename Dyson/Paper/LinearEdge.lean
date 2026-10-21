import Dyson.Paper.LinearEdgeLocal
import Dyson.Paper.MeasureRepresentation

/-! Literal revised M6 edge clauses, through actual M5 Poisson profiles,
Perron identities, the beta expansion and its spectral inverse. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearEdge
open Full Full.ExternalAlgebraic Full.Singularities Full.Spectral Full.PerronContinuation

theorem edge_symmetric {n : ℕ} (hn : 0 < n)
    (stieltjes : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S) (hsym : ∀ i j, S i j = S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ δ c C : ℝ,0<δ ∧ 0<c ∧ 0<C ∧
      ∀ (z : ℂ) (hz : 0<z.im),|z.re-τ|≤δ →
        c*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2))≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
          C*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨μ,hμ⟩ := MeasureRepresentation.upper_solution_probability_representation stieltjes
    S a hS m hupper heq
  obtain ⟨frame⟩ := regular_frontier_varying_frame continuousPerron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  obtain ⟨D,hp,hr,hl⟩ := SingularitiesFrontier.data_with_perron_symmetric hn algebraic puiseux
    S a hS hirr hsym m hupper heq τ i hfront hτ frame.r₀ frame.l₀ frame.center
  obtain ⟨b,B,hb,hB,hnd⟩ := SingularitiesUniform.uniform_nondegeneracy_symmetric hn algebraic puiseux
    S a hS hirr hsym m hupper heq τ i hfront hτ frame
  obtain ⟨ci,Ci,hci,hCi,hinv⟩ := LinearFrame.edge_inverse_with_frame hn spectral normalForm orientation
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ hedge frame D hr hl B hB
    (by simpa only [hp] using hnd.mono (fun _ h => h.2))
  obtain ⟨left,profiles⟩ := SingularityPoissonModel.edge_symmetric perron normalForm orientation hn
    algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ inversion hedge μ
      (fun j => (hμ j).1) (fun j => (hμ j).2)
  obtain ⟨c,C,hc,hC,hprofile⟩ := LinearEdgePoisson.sum_profiles hn m τ left profiles
  obtain ⟨lo,hi,hlo,hhi,hlocal⟩ := LinearFrame.edge_local_from_poisson hn algebraic puiseux
    S a hS m hupper heq τ hτ frame D.nonzero ci Ci hci hCi hinv left c C hc hC hprofile
  apply MainLinearSingular.singular_full_height_of_eventual S a m hS hupper heq
    τ ((1:ℝ)/2) (lo/2) hi (by norm_num) (by positivity) hhi
  filter_upwards [hlocal] with z hzlocal
  intro hz
  exact LinearFrame.sqrt_local_to_distance hz hlo.le hhi.le (hzlocal hz)

theorem edge_nonbacktracking {n : ℕ} (hn : 0 < n)
    (stieltjes : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (perron : ExternalPerronExistence) (continuousPerron : ExternalContinuousPerron)
    (spectral : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀ i j, S i j = G.matrix (e i) (e j))
    (hpot : ∀ i, a i = av (G.head (e i)))
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ δ c C : ℝ,0<δ ∧ 0<c ∧ 0<C ∧
      ∀ (z : ℂ) (hz : 0<z.im),|z.re-τ|≤δ →
        c*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2))≤
          ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
          C*max 1 (1/(|z.re-τ|+z.im)^((1:ℝ)/2)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨μ,hμ⟩ := MeasureRepresentation.upper_solution_probability_representation stieltjes
    S a hS m hupper heq
  obtain ⟨frame⟩ := regular_frontier_varying_frame continuousPerron hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  obtain ⟨D,hp,hr,hl⟩ := SingularitiesFrontier.data_with_perron_nonbacktracking hn algebraic puiseux
    S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ frame.r₀ frame.l₀ frame.center
  obtain ⟨b,B,hb,hB,hnd⟩ := SingularitiesUniform.uniform_nondegeneracy_nonbacktracking hn algebraic puiseux
    S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ frame
  obtain ⟨ci,Ci,hci,hCi,hinv⟩ := LinearFrame.edge_inverse_with_frame hn spectral normalForm orientation
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ hedge frame D hr hl B hB
    (by simpa only [hp] using hnd.mono (fun _ h => h.2))
  obtain ⟨left,profiles⟩ := SingularityPoissonModel.edge_nonbacktracking perron normalForm orientation hn
    algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ inversion hedge μ
      (fun j => (hμ j).1) (fun j => (hμ j).2)
  obtain ⟨c,C,hc,hC,hprofile⟩ := LinearEdgePoisson.sum_profiles hn m τ left profiles
  obtain ⟨lo,hi,hlo,hhi,hlocal⟩ := LinearFrame.edge_local_from_poisson hn algebraic puiseux
    S a hS m hupper heq τ hτ frame D.nonzero ci Ci hci hCi hinv left c C hc hC hprofile
  apply MainLinearSingular.singular_full_height_of_eventual S a m hS hupper heq
    τ ((1:ℝ)/2) (lo/2) hi (by norm_num) (by positivity) hhi
  filter_upwards [hlocal] with z hzlocal
  intro hz
  exact LinearFrame.sqrt_local_to_distance hz hlo.le hhi.le (hzlocal hz)

end NonSymmetricDyson.Paper.LinearEdge
