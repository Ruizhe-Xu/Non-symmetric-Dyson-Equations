import Dyson.Full.PerronVarying
import Dyson.Full.SpectralConsequences

/-! Revised manuscript's boundary conventions. The value of η/δ is defined
by the continuous formula even at δ=0, and agrees with the usual quotient
wherever that quotient is defined. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Singularities Full.SingularSpectral
variable {ι : Type*} [Fintype ι]

def mu (l : ι → ℝ) (m : ι → ℂ) : ℝ := ∑ i,l i*‖m i‖
def extendedHeightRatio (lam : ℝ) (l : ι → ℝ) (m : ι → ℂ) : ℝ := (1-lam)/mu l m

theorem mu_positive [Nonempty ι] (l : ι → ℝ) (m : ι → ℂ)
    (hl : ∀ i,0<l i) (hm : ∀ i,m i≠0) : 0 < mu l m :=
  Finset.sum_pos (fun i _ => mul_pos (hl i) (norm_pos_iff.mpr (hm i))) Finset.univ_nonempty

/-- The quotient extension agrees with η/δ at every point of positive δ,
using the actual imaginary Dyson identity. -/
theorem extendedHeightRatio_eq [Nonempty ι]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hm : ∀ i,m i≠0) (heq : BasicEstimates.IsDysonSolution S a z m)
    (l : ι → ℝ) (lam : ℝ) (hl : ∀ i,0<l i)
    (hleft : ∀ j,∑ i,l i*(‖m i‖*S i j*‖m j‖)=lam*l j)
    (hδ : perronDensity l m≠0) : extendedHeightRatio lam l m=z.im/perronDensity l m := by
  have hμ := mu_positive l m hl hm
  have h := perron_density_identity S a z m hm heq l lam hleft
  apply (div_eq_div_iff hμ.ne' hδ).mpr
  exact h

theorem mu_tendsto {X : Type*} {L : Filter X}
    (l : X → ι → ℝ) (m : X → ι → ℂ) (l₀ : ι → ℝ) (m₀ : ι → ℂ)
    (hl : Tendsto l L (𝓝 l₀)) (hm : Tendsto m L (𝓝 m₀)) :
    Tendsto (fun x => mu (l x) (m x)) L (𝓝 (mu l₀ m₀)) := by
  apply tendsto_finset_sum
  intro i _
  exact ((tendsto_pi_nhds.mp hl) i).mul (((tendsto_pi_nhds.mp hm) i).norm)

/-- Continuous extension on an arbitrary parameter domain. -/
theorem extendedHeightRatio_continuousAt {X : Type*} [TopologicalSpace X]
    (lam : X → ℝ) (l : X → ι → ℝ) (m : X → ι → ℂ) (x : X)
    (hlam : ContinuousAt lam x) (hl : ContinuousAt l x) (hm : ContinuousAt m x)
    (hμ : mu (l x) (m x)≠0) :
    ContinuousAt (fun y => extendedHeightRatio (lam y) (l y) (m y)) x := by
  exact (tendsto_const_nhds.sub hlam).div (mu_tendsto l m (l x) (m x) hl hm) hμ

/-- Original smallness argument at a regular edge/cusp: continuity of λ and
μ, not an undefined 0/0 quotient, yields the limit zero on the closed upper side. -/
theorem varying_frame_heightRatio_limit {X : Type*} {n : ℕ} (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ) (m : X → Fin n → ℂ) (L : Filter X)
    (m₀ : Fin n → ℂ) (d : PerronContinuation.VaryingFrame S m L m₀)
    (hm : Tendsto m L (𝓝 m₀)) (hm₀ : ∀ i,m₀ i≠0) :
    Tendsto (fun x => extendedHeightRatio (d.lam x) (d.l x) (m x)) L (𝓝 0) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hμ := mu_positive d.l₀ m₀ d.center.left_positive hm₀
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub d.lam_limit).div
    (mu_tendsto d.l m d.l₀ m₀ d.left_limit hm) hμ.ne'
  simpa [extendedHeightRatio] using hh

/-- Actual manuscript application, with the limiting boundary value and
Perron frame supplied by the already proved regular frontier construction. -/
theorem regular_frontier_heightRatio_extension
    (perron : PerronContinuation.ExternalContinuousPerron)
    {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ d : PerronContinuation.VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ)),
      Tendsto (fun z => extendedHeightRatio (d.lam z) (d.l z) (Boundary.boundaryVector m z))
        (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (𝓝 0) := by
  obtain ⟨d⟩ := PerronContinuation.regular_frontier_varying_frame perron hn algebraic puiseux
    S a hS hirr m hupper heq τ i hfront hτ
  exact ⟨d,varying_frame_heightRatio_limit hn S _ _ _ d
    (PerronContinuation.regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
    (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1⟩

end NonSymmetricDyson.Paper.Spectral
