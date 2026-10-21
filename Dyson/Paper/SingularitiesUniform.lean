import Dyson.Paper.SingularitiesFrontierNB

/-! Proposition psi-positive-and-nondegenerate: the actual full closed-upper
uniform bound, using the original Sym/NB Jensen/reflection proof at the center
and the proved continuity of Perron vectors and the restricted inverse. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace NonSymmetricDyson.Paper.SingularitiesUniform
open Full Full.Singularities Full.PerronContinuation
variable {n : ℕ}

theorem coefficient_positive_symmetric
    (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (r l u : Fin n → ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) 1 r l)
    (horth : ∑ j,l j*u j=0)
    (hu : ∀ j,u j-∑ k,saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)) j k*u k=
      ((Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖)*r j^2-
      r j*quadraticCoefficient
        (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r) :
    0<(quadraticCoefficient
      (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r)^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)))
        (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r u := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  let b : Fin n → ℝ := fun j => (m₀ j).re
  let q : Fin n → ℝ := fun j => ‖m₀ j‖
  let p : Fin n → ℝ := fun j => b j / q j
  change ∀ j,u j-∑ k,saturatedMatrix S m₀ j k*u k=p j*r j^2-r j*quadraticCoefficient p l r at hu
  have hreal : ∀ j, (m₀ j).im = 0 :=
    Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hboundary := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hnz : ∀ j, m₀ j ≠ 0 := hboundary.1
  have hcast : (fun j => (b j : ℂ)) = m₀ := by
    funext j
    apply Complex.ext
    · rfl
    · simp [hreal]
  have hqpos : ∀ j, 0 < q j := fun j => norm_pos_iff.mpr (hnz j)
  have hqabs (j : Fin n) : q j = |b j| := by
    dsimp [q]
    rw [← congrFun hcast j, Complex.norm_real, Real.norm_eq_abs]
  have hq2 (j : Fin n) : q j ^ 2 = b j ^ 2 := by rw [hqabs, sq_abs]
  have hp2 (j : Fin n) : p j ^ 2 = 1 := by
    dsimp [p]
    rw [div_pow, ← hq2, div_self (pow_ne_zero 2 (hqpos j).ne')]
  have hpq (j : Fin n) : q j = p j * b j := by
    dsimp [p]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hqpos j).ne').mpr
    convert hq2 j using 1 <;> ring
  have hFr : ∀ j,∑ k,saturatedMatrix S m₀ j k*r k=r j := by simpa using hd.right_eigen
  have hlF : ∀ k,∑ j,l j*saturatedMatrix S m₀ j k=l k := by simpa using hd.left_eigen
  have hbpq (j : Fin n) : b j=p j*q j := by
    rw [hpq, ← mul_assoc, ← pow_two, hp2, one_mul]
  have hrealEq : ∀ j,-(b j)⁻¹=τ-a j+∑ k,S j k*b k := by
    have hh : BasicEstimates.IsDysonSolution S a (τ : ℂ) (fun j => (b j : ℂ)) := by
      rw [hcast]
      exact hboundary.2.2
    intro j
    simpa using congrArg Complex.re (hh j)
  have hnot := SingularitiesFrontier.potential_not_identically_frontier hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  have hψ := cubicCoefficient_nonnegative_projected (saturatedMatrix S m₀) p l r u 1
    (quadraticCoefficient p l r) (saturatedMatrix_nonnegative S hS m₀)
    hd.left_positive hd.right_positive (by norm_num) (by norm_num)
    hd.right_eigen hd.left_eigen horth (by simpa [mul_comm] using hu)
  by_cases hz : quadraticCoefficient p l r=0
  · have hpos : 0<cubicCoefficient (saturatedMatrix S m₀) p l r u := by
      exact SingularitiesNondegenerate.symmetric_positive S a b p q r l u τ hS hsym hp2 hqpos
        hd.right_positive hd.left_positive hbpq hFr hlF (by simpa [hz] using hu) hrealEq hnot
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hpos
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hz) hψ

theorem uniform_nondegeneracy_symmetric
    (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (hsym : ∀ i j,S i j=S j i)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) :
    let p := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
      c≤(quadraticCoefficient p (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
          (stableCoefficient p (d.r z) (d.K z)) ∧
      (quadraticCoefficient p (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
          (stableCoefficient p (d.r z) (d.K z))≤C := by
  letI : Nonempty (Fin n) := ⟨i⟩
  dsimp only
  apply d.uniform_nondegeneracy (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
  intro u ho hu
  exact coefficient_positive_symmetric hn algebraic puiseux S a hS hirr hsym m
    hupper heq τ i hfront hτ d.r₀ d.l₀ u d.center ho hu


theorem coefficient_positive_nonbacktracking
    (hn : 0<n)
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
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (r l u : Fin n → ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) 1 r l)
    (horth : ∑ j,l j*u j=0)
    (hu : ∀ j,u j-∑ k,saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)) j k*u k=
      ((Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖)*r j^2-
      r j*quadraticCoefficient
        (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r) :
    0<(quadraticCoefficient
      (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r)^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)))
        (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) l r u := by
  letI : Nonempty (Fin n) := ⟨i⟩
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  let b : Fin n → ℝ := fun j => (m₀ j).re
  let q : Fin n → ℝ := fun j => ‖m₀ j‖
  let p : Fin n → ℝ := fun j => b j / q j
  change ∀ j,u j-∑ k,saturatedMatrix S m₀ j k*u k=p j*r j^2-r j*quadraticCoefficient p l r at hu
  have hreal : ∀ j, (m₀ j).im = 0 :=
    Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hboundary := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hnz : ∀ j, m₀ j ≠ 0 := hboundary.1
  have hcast : (fun j => (b j : ℂ)) = m₀ := by
    funext j
    apply Complex.ext
    · rfl
    · simp [hreal]
  have hqpos : ∀ j, 0 < q j := fun j => norm_pos_iff.mpr (hnz j)
  have hqabs (j : Fin n) : q j = |b j| := by
    dsimp [q]
    rw [← congrFun hcast j, Complex.norm_real, Real.norm_eq_abs]
  have hq2 (j : Fin n) : q j ^ 2 = b j ^ 2 := by rw [hqabs, sq_abs]
  have hp2 (j : Fin n) : p j ^ 2 = 1 := by
    dsimp [p]
    rw [div_pow, ← hq2, div_self (pow_ne_zero 2 (hqpos j).ne')]
  have hpq (j : Fin n) : q j = p j * b j := by
    dsimp [p]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (hqpos j).ne').mpr
    convert hq2 j using 1 <;> ring
  have hFr : ∀ j,∑ k,saturatedMatrix S m₀ j k*r k=r j := by simpa using hd.right_eigen
  have hlF : ∀ k,∑ j,l j*saturatedMatrix S m₀ j k=l k := by simpa using hd.left_eigen
  have hbpq (j : Fin n) : b j=p j*q j := by
    rw [hpq, ← mul_assoc, ← pow_two, hp2, one_mul]
  have hrealEq : ∀ j,-(b j)⁻¹=τ-a j+∑ k,S j k*b k := by
    have hh : BasicEstimates.IsDysonSolution S a (τ : ℂ) (fun j => (b j : ℂ)) := by
      rw [hcast]
      exact hboundary.2.2
    intro j
    simpa using congrArg Complex.re (hh j)
  have hnot := SingularitiesFrontier.potential_not_identically_frontier hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ
  have hψ := cubicCoefficient_nonnegative_projected (saturatedMatrix S m₀) p l r u 1
    (quadraticCoefficient p l r) (saturatedMatrix_nonnegative S hS m₀)
    hd.left_positive hd.right_positive (by norm_num) (by norm_num)
    hd.right_eigen hd.left_eigen horth (by simpa [mul_comm] using hu)
  by_cases hz : quadraticCoefficient p l r=0
  · have hpos : 0<cubicCoefficient (saturatedMatrix S m₀) p l r u := by
      exact SingularitiesReindex.nb_positive_reindex G deg e S a av hmat hpot τ b p q r l u hp2 hqpos
        hd.right_positive hd.left_positive hbpq hFr hlF (by simpa [hz] using hu) hrealEq hnot
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hpos
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hz) hψ

theorem uniform_nondegeneracy_nonbacktracking
    (hn : 0<n)
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
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) :
    let p := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
      c≤(quadraticCoefficient p (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
          (stableCoefficient p (d.r z) (d.K z)) ∧
      (quadraticCoefficient p (d.l z) (d.r z))^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
          (stableCoefficient p (d.r z) (d.K z))≤C := by
  letI : Nonempty (Fin n) := ⟨i⟩
  dsimp only
  apply d.uniform_nondegeneracy (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
  intro u ho hu
  exact coefficient_positive_nonbacktracking hn algebraic puiseux S a hS hirr G deg e av hmat hpot m
    hupper heq τ i hfront hτ d.r₀ d.l₀ u d.center ho hu


theorem psi_nonnegative_upper [Nonempty (Fin n)]
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (p r l : Fin n → ℝ) (lam : ℝ)
    (hd : PerronData (saturatedMatrix S m) lam r l)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse (complexMatrixOperator (saturatedMatrix S m)).toLinearMap
      K.toLinearMap (complexFunctional l).toLinearMap (fun i => (r i:ℂ))) :
    0≤cubicCoefficient (saturatedMatrix S m) p l r (stableCoefficient p r K) := by
  exact actual_cubic_positive_upper S a z m hS hz hm heq p r l lam hd K hK

end NonSymmetricDyson.Paper.SingularitiesUniform
