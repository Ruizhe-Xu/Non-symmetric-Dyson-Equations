import Dyson.Full.MainNonlinearFrontier
import Dyson.Full.SingularityTopology

/-! The original Lyapunov–Schmidt, root-product, and continuation proof of M7.
The actual frontier data are supplied by the original Jensen/NB argument in
`Paper.SingularitiesFrontierNB`, rather than reconstructed by another proof.
The auxiliary data are consumed by the actual model theorem below; they are
not external mathematical assumptions. -/
noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace NonSymmetricDyson.Paper.Nonlinear
open Full Full.Nonlinear Full.Singularities
variable {n : ℕ}

theorem regular_frontier_of_data
    (Hmax : ℝ) (hHmax : 0 < Hmax)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (ift : AnalyticImplicitFunctionPrinciple (Fin n → ℂ) (ℂ × (Fin n → ℂ)))
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) :
    ∃ k : ℕ, ∃ H r c₀ C : ℝ,
      ((k = 2 ∧ quadraticCoefficient d.p d.l d.r ≠ 0) ∨
       (k = 3 ∧ quadraticCoefficient d.p d.l d.r = 0 ∧
         0 < cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)))
           d.p d.l d.r d.u)) ∧
      0 < H ∧ H ≤ Hmax ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → Fin n → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ (1 - (1 : ℝ) / k) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ := Boundary.boundaryVector m (τ : ℂ)
  let mbar := Boundary.boundaryVector m
  obtain ⟨k, hcase, ⟨D⟩⟩ := frontier_localReduction_exists ift rootArgument S m₀ d
  have hk : 2 ≤ k := by rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _, _⟩ <;> omega
  obtain ⟨hq0, hp, hq⟩ := frontier_scale_identity d
  have hboundary := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hmcont : ContinuousWithinAt mbar {z : ℂ | 0 ≤ z.im} (τ : ℂ) :=
    regular_extension_continuousWithinAt algebraic puiseux S a hS m hupper heq τ hτ
  have hbar : ∀ z : ℂ, 0 < z.im → mbar z = m z :=
    Boundary.family_extension_agrees S a hS m hupper heq
  obtain ⟨H, r, c₀, C, hH, hHmax', hr, hc₀, hC, hbound⟩ :=
    nonlinear_boundary_main_of_reduction_below Hmax hHmax S a hS τ mbar m₀ (fun j => (d.p j : ℂ))
      (frontierScale m₀) (fun j => (d.r j : ℂ))
      (complexMatrixOperator (saturatedMatrix S m₀)) d.K.toContinuousLinearMap
      (complexFunctional d.l) k hk D (frontier_operator_scaled S m₀)
      hboundary.2.2 d.nonzero hq0 hp hq rfl hmcont
      (fun z hz => by rw [hbar z hz]; exact hupper z hz)
      (fun z hz => by rw [hbar z hz]; exact heq z hz)
  refine ⟨k, H, r, c₀, C, hcase, hH, hHmax', hr, hc₀, hC, ?_⟩
  intro x η η₀ E g htop hx hη hηH hE hgcont hg0 hclose hres
  have hsub : Icc η H ⊆ Icc η η₀ := fun t ht => ⟨ht.1, ht.2.trans htop⟩
  have hpositive : ∀ t ∈ Icc η H, 0 < (verticalPoint x t).im :=
    fun t ht => hη.trans_le ht.1
  have hh := hbound x η E g hx hη hηH hE (hgcont.mono hsub)
    (fun t ht => hg0 t (hsub ht))
    (fun t ht => by rw [hbar _ (hpositive t ht)]; exact hclose t (hsub ht))
    (fun t ht => hres t (hsub ht))
  rw [hbar _ hη] at hh
  exact hh


end NonSymmetricDyson.Paper.Nonlinear
