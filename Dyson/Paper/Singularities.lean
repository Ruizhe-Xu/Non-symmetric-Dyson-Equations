import Dyson.Paper.SingularitiesFrontierNB
import Dyson.Full.MainSingularityEndpoints

/-! The revised fifth main theorem: both edge and cusp statements carry
(Sym) or the actual non-backtracking hypotheses. Nondegeneracy is supplied
by the original Jensen/terminal/reflection proof. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Paper.Singularities
open Full Full.Singularities SingularitiesFrontier

section Symmetric

variable {n : ℕ}
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (hn : 0 < n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable (hsym : ∀ i j,S i j=S j i)
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)

include hsym perron normalForm orientation hn algebraic puiseux hS hirr hupper heq hfront hτ

/-- At a topologically defined regular edge, the true density has the
square-root law on its interior side and is identically zero outside. -/
theorem regular_edge_symmetric
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : Fin n → ℝ) (C : ℝ), c ≠ 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        (c * (x - τ) < 0 →
          |Boundary.realDensity m j x - D j * rootRadius c 2 (x - τ)| ≤
            C * (rootRadius c 2 (x - τ)) ^ 2 ∧ 0 < Boundary.realDensity m j x) ∧
        (0 < c * (x - τ) → Boundary.realDensity m j x = 0) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨D⟩ := symmetric_frontier_data perron hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ
  obtain ⟨P,_,_⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ D
  have hk := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P).1.mpr hedge
  have hb0 : Boundary.boundaryVector m (τ : ℂ) =
      (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  refine ⟨P.coefficient, fun j => P.tangent j / Real.pi, P.errorConstant / Real.pi,
    P.coefficient_ne_zero, fun j => div_pos (P.tangent_pos j) Real.pi_pos,
    div_pos P.errorConstant_pos Real.pi_pos, ?_⟩
  filter_upwards [P.quadratic_boundary_density hk
    (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont
    (hblocal.mono fun _ h => h.2)] with x hx j
  constructor
  · intro hs
    have hh := (hx j).1 hs
    exact ⟨density_normalize_error _ _ _ _ hh.1, div_pos hh.2 Real.pi_pos⟩
  · intro hs
    exact div_eq_zero_iff.mpr (Or.inl ((hx j).2 hs))

/-- At a topologically defined regular cusp, the true density has the
cubic-root law and is positive on both punctured sides. -/
theorem regular_cusp_symmetric
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : Fin n → ℝ) (C : ℝ), c < 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        |Boundary.realDensity m j x - D j * rootRadius c 3 (x - τ)| ≤
          C * (rootRadius c 3 (x - τ)) ^ 2 ∧
        (x ≠ τ → 0 < Boundary.realDensity m j x) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨D⟩ := symmetric_frontier_data perron hn algebraic puiseux S a hS hirr hsym m hupper heq τ i hfront hτ
  obtain ⟨P,_,_⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ D
  have hk := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P).2.mpr hcusp
  have hb0 : Boundary.boundaryVector m (τ : ℂ) =
      (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  refine ⟨P.coefficient, fun j => (P.tangent j * (Real.sqrt 3 / 2)) / Real.pi,
    P.errorConstant / Real.pi, P.cubic_negative hk, ?_,
    div_pos P.errorConstant_pos Real.pi_pos, ?_⟩
  · intro j
    exact div_pos (mul_pos (P.tangent_pos j)
      (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))) Real.pi_pos
  · filter_upwards [P.cubic_boundary_density hk
      (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont
      (hblocal.mono fun _ h => h.2)] with x hx j
    exact ⟨density_normalize_error _ _ _ _ (hx j).1,
      fun hne => div_pos ((hx j).2 hne) Real.pi_pos⟩

end Symmetric

section Nonbacktracking

variable {n : ℕ}
variable (perron : ExternalPerronExistence)
variable (normalForm : RealAnalyticMonomialNormalFormPrinciple)
variable (orientation : RealHolomorphicOrientationPrinciple)
variable (hn : 0 < n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
variable (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
variable (av : V → ℝ) (hmat : ∀ i j,S i j=G.matrix (e i) (e j))
variable (hpot : ∀ i,a i=av (G.head (e i)))
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
variable (hτ : τ ∉ Boundary.singularUnion m)

include deg hmat hpot perron normalForm orientation hn algebraic puiseux hS hirr hupper heq hfront hτ

/-- At a topologically defined regular edge, the true density has the
square-root law on its interior side and is identically zero outside. -/
theorem regular_edge_nonbacktracking
    (hedge : IsRegularEdge (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : Fin n → ℝ) (C : ℝ), c ≠ 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        (c * (x - τ) < 0 →
          |Boundary.realDensity m j x - D j * rootRadius c 2 (x - τ)| ≤
            C * (rootRadius c 2 (x - τ)) ^ 2 ∧ 0 < Boundary.realDensity m j x) ∧
        (0 < c * (x - τ) → Boundary.realDensity m j x = 0) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨D⟩ := nb_frontier_data perron hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ
  obtain ⟨P,_,_⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ D
  have hk := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P).1.mpr hedge
  have hb0 : Boundary.boundaryVector m (τ : ℂ) =
      (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  refine ⟨P.coefficient, fun j => P.tangent j / Real.pi, P.errorConstant / Real.pi,
    P.coefficient_ne_zero, fun j => div_pos (P.tangent_pos j) Real.pi_pos,
    div_pos P.errorConstant_pos Real.pi_pos, ?_⟩
  filter_upwards [P.quadratic_boundary_density hk
    (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont
    (hblocal.mono fun _ h => h.2)] with x hx j
  constructor
  · intro hs
    have hh := (hx j).1 hs
    exact ⟨density_normalize_error _ _ _ _ hh.1, div_pos hh.2 Real.pi_pos⟩
  · intro hs
    exact div_eq_zero_iff.mpr (Or.inl ((hx j).2 hs))

/-- At a topologically defined regular cusp, the true density has the
cubic-root law and is positive on both punctured sides. -/
theorem regular_cusp_nonbacktracking
    (hcusp : IsRegularCusp (Boundary.regularSupport m i) τ) :
    ∃ (c : ℝ) (D : Fin n → ℝ) (C : ℝ), c < 0 ∧ (∀ j, 0 < D j) ∧ 0 < C ∧
      ∀ᶠ x in 𝓝 τ, ∀ j,
        |Boundary.realDensity m j x - D j * rootRadius c 3 (x - τ)| ≤
          C * (rootRadius c 3 (x - τ)) ^ 2 ∧
        (x ≠ τ → 0 < Boundary.realDensity m j x) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨D⟩ := nb_frontier_data perron hn algebraic puiseux S a hS hirr G deg e av hmat hpot m hupper heq τ i hfront hτ
  obtain ⟨P,_,_⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ D
  have hk := (regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P).2.mpr hcusp
  have hb0 : Boundary.boundaryVector m (τ : ℂ) =
      (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  refine ⟨P.coefficient, fun j => (P.tangent j * (Real.sqrt 3 / 2)) / Real.pi,
    P.errorConstant / Real.pi, P.cubic_negative hk, ?_,
    div_pos P.errorConstant_pos Real.pi_pos, ?_⟩
  · intro j
    exact div_pos (mul_pos (P.tangent_pos j)
      (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))) Real.pi_pos
  · filter_upwards [P.cubic_boundary_density hk
      (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont
      (hblocal.mono fun _ h => h.2)] with x hx j
    exact ⟨density_normalize_error _ _ _ _ (hx j).1,
      fun hne => div_pos ((hx j).2 hne) Real.pi_pos⟩

end Nonbacktracking

end NonSymmetricDyson.Paper.Singularities
