import Dyson.Paper.SingularitiesNondegenerate
import Dyson.Full.SingularitiesFrontierData

/-! Actual boundary-data assembly using the revised paper's original
symmetric Jensen/reflection argument. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.SingularitiesFrontier
open Full Full.Singularities

/-- A regular zero-density support frontier cannot have a potential
identically equal to its energy: uniqueness makes the vertical solution
purely imaginary, contradicting the real nonzero boundary value. -/
theorem potential_not_identically_frontier
    {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) : ¬∀ j,a j=τ := by
  intro ha
  have hb := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hr := Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have ht := (Boundary.regular_boundary_continuous_and_limits algebraic puiseux
    S a hS m hupper heq τ hτ).2.self_of_nhds
  let z : ℝ → ℂ := fun η => (τ : ℂ)+(η : ℂ)*Complex.I
  have hzupper (η : ℝ) (hη : 0<η) : z η∈ExternalAlgebraic.upper := by
    simpa [z,ExternalAlgebraic.upper] using hη
  have hzt : Tendsto z (𝓝[Set.Ioi 0] 0) (𝓝[ExternalAlgebraic.upper] (τ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous z := by unfold z;fun_prop
      simpa [z] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact hzupper η hη
  exact SingularitiesNondegenerate.constant_potential_limit_impossible S a τ
    (fun η => m (z η)) (Boundary.boundaryVector m (τ : ℂ)) hS ha
    (fun η hη => hupper _ (hzupper η hη))
    (fun η hη => heq _ (hzupper η hη)) (ht.2.comp hzt) hr i (hb.1 i)

/-- Full actual FrontierData under (Sym), constructed without calling the
alternative general-irreducible Möbius nondegeneracy theorem. -/
theorem symmetric_frontier_data (perron : ExternalPerronExistence)
    {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    Nonempty (FrontierData S (Boundary.boundaryVector m (τ : ℂ))) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  let b : Fin n → ℝ := fun j => (m₀ j).re
  let q : Fin n → ℝ := fun j => ‖m₀ j‖
  let p : Fin n → ℝ := fun j => b j/q j
  have hreal : ∀ j,(m₀ j).im=0 :=
    Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hb := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hnz : ∀ j,m₀ j≠0 := hb.1
  have hcast : (fun j => (b j : ℂ))=m₀ := by
    funext j
    apply Complex.ext
    · rfl
    · simp [hreal]
  have hqpos : ∀ j,0<q j := fun j => norm_pos_iff.mpr (hnz j)
  have hqabs (j : Fin n) : q j=|b j| := by
    dsimp [q]
    rw [← congrFun hcast j,Complex.norm_real,Real.norm_eq_abs]
  have hq2 (j : Fin n) : q j^2=b j^2 := by rw [hqabs,sq_abs]
  have hp2 (j : Fin n) : p j^2=1 := by
    dsimp [p]
    rw [div_pow,← hq2,div_self (pow_ne_zero 2 (hqpos j).ne')]
  have hpq (j : Fin n) : q j=p j*b j := by
    dsimp [p]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hqpos j).ne').mpr
    convert hq2 j using 1 <;> ring
  have hbpq (j : Fin n) : b j=p j*q j := by
    rw [hpq, ← mul_assoc, ← pow_two, hp2, one_mul]
  obtain ⟨r,l,hr,hl,hnorm,hFr,hlF,hsimple⟩ :=
    regular_frontier_perron_data perron hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  obtain ⟨K,u,hK,huK,hul,hu,hσ,hψ⟩ :=
    quadratic_stable_data_exists (saturatedMatrix S m₀) p r l hnorm hFr hlF hsimple
  have hrealEq : ∀ j,-(b j)⁻¹=τ-a j+∑ k,S j k*b k := by
    have hh : BasicEstimates.IsDysonSolution S a (τ : ℂ) (fun j => (b j : ℂ)) := by
      rw [hcast]
      exact hb.2.2
    intro j
    have hj := congrArg Complex.re (hh j)
    simpa using hj
  have hnot := potential_not_identically_frontier hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hnondeg : quadraticCoefficient p l r≠0 ∨
      0<cubicCoefficient (saturatedMatrix S m₀) p l r u := by
    by_cases hz : quadraticCoefficient p l r=0
    · right
      exact SingularitiesNondegenerate.symmetric_positive S a b p q r l u τ hS hsym hp2 hqpos
        hr hl hbpq hFr hlF (by simpa [hz] using hu) hrealEq hnot
    · exact Or.inl hz
  exact ⟨⟨p,r,l,u,K,hreal,hnz,hp2,hpq,hr,hl,hnorm,hFr,hlF,hsimple,
    hK,huK,hul,hu,hσ,hψ,hnondeg⟩⟩

end NonSymmetricDyson.Paper.SingularitiesFrontier
