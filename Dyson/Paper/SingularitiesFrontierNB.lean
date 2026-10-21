import Dyson.Paper.SingularitiesFrontier
import Dyson.Paper.SingularitiesReindex

/-! Actual NB frontier data from the original Jensen/reflection argument. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.SingularitiesFrontier
open Full Full.Singularities

theorem nb_frontier_data (perron : ExternalPerronExistence)
    {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    {V : Type*} [Fintype V] (G : Nonbacktracking.BaseGraph V)
    (deg : Full.BulkGraph.NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (av : V → ℝ) (hmat : ∀ i j,S i j=G.matrix (e i) (e j))
    (hpot : ∀ i,a i=av (G.head (e i)))
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
      exact SingularitiesReindex.nb_positive_reindex G deg e S a av hmat hpot τ b p q r l u hp2 hqpos
        hr hl hbpq hFr hlF (by simpa [hz] using hu) hrealEq hnot
    · exact Or.inl hz
  exact ⟨⟨p,r,l,u,K,hreal,hnz,hp2,hpq,hr,hl,hnorm,hFr,hlF,hsimple,
    hK,huK,hul,hu,hσ,hψ,hnondeg⟩⟩

end NonSymmetricDyson.Paper.SingularitiesFrontier
