import Dyson.Paper.SingularitiesFrontierNB

/-! Actual singularity data with a prescribed normalized Perron frame.
This makes coefficient/topology statements apply to the same moving frame
used in the spectral expansion, without a normalization change. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.SingularitiesFrontier
open Full Full.Singularities Full.PerronContinuation

theorem data_with_perron_symmetric
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
    (hτ : τ∉Boundary.singularUnion m)
    (r l : Fin n → ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ))) 1 r l) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
      D.p=(fun j => (Boundary.boundaryVector m (τ : ℂ) j).re/‖Boundary.boundaryVector m (τ : ℂ) j‖) ∧
      D.r=r ∧ D.l=l := by
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
  have hr := hd.right_positive
  have hl := hd.left_positive
  have hnorm := hd.normalized
  have hFr : ∀ j,∑ k,saturatedMatrix S m₀ j k*r k=r j := by simpa using hd.right_eigen
  have hlF : ∀ k,∑ j,l j*saturatedMatrix S m₀ j k=l k := by simpa using hd.left_eigen
  have hsimple : ∀ x:Fin n → ℂ,complexMatrixOperator (saturatedMatrix S m₀) x=x →
      x=complexFunctional l x • (fun j => (r j:ℂ)) := fun x hx => hd.simple x (by simpa using hx)
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
    hK,huK,hul,hu,hσ,hψ,hnondeg⟩,rfl,rfl,rfl⟩


theorem data_with_perron_nonbacktracking
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
    (hτ : τ∉Boundary.singularUnion m)
    (r l : Fin n → ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ))) 1 r l) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
      D.p=(fun j => (Boundary.boundaryVector m (τ : ℂ) j).re/‖Boundary.boundaryVector m (τ : ℂ) j‖) ∧
      D.r=r ∧ D.l=l := by
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
  have hr := hd.right_positive
  have hl := hd.left_positive
  have hnorm := hd.normalized
  have hFr : ∀ j,∑ k,saturatedMatrix S m₀ j k*r k=r j := by simpa using hd.right_eigen
  have hlF : ∀ k,∑ j,l j*saturatedMatrix S m₀ j k=l k := by simpa using hd.left_eigen
  have hsimple : ∀ x:Fin n → ℂ,complexMatrixOperator (saturatedMatrix S m₀) x=x →
      x=complexFunctional l x • (fun j => (r j:ℂ)) := fun x hx => hd.simple x (by simpa using hx)
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
    hK,huK,hul,hu,hσ,hψ,hnondeg⟩,rfl,rfl,rfl⟩

end NonSymmetricDyson.Paper.SingularitiesFrontier
