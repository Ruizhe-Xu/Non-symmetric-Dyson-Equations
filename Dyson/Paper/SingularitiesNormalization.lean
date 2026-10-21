import Dyson.Paper.SingularitiesPrescribed
import Dyson.Full.PerronBounds

/-! The paper's two simultaneous normalizations are imposed on the actual
Perron data before constructing the stable vector and cubic coefficients. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.SingularitiesNormalization
open Full Full.Singularities Full.PerronContinuation

/-- Rescale a positive simple Perron pair, including its exact projection,
so that the right vector has Euclidean norm one and the dual pairing stays one. -/
theorem normalized_perron_data_explicit {n : ℕ} (hn : 0<n)
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (r l : Fin n → ℝ)
    (hd : PerronData A lam r l) :
    let d : ℝ := Real.sqrt (∑ j,r j^2)
    let R : Fin n → ℝ := fun j => r j/d
    let L : Fin n → ℝ := fun j => d*l j
    PerronData A lam R L ∧
      (∑ j,R j^2=1) ∧ ‖(WithLp.toLp 2 R : EuclideanSpace ℝ (Fin n))‖=1 := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let d : ℝ := Real.sqrt (∑ j,r j^2)
  have hsum : 0<∑ j,r j^2 := Finset.sum_pos (fun j _ => sq_pos_of_pos (hd.right_positive j))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hn⟩⟩)
  have hdp : 0<d := Real.sqrt_pos.mpr hsum
  have hdsq : d^2=∑ j,r j^2 := Real.sq_sqrt hsum.le
  let R : Fin n → ℝ := fun j => r j/d
  let L : Fin n → ℝ := fun j => d*l j
  have hnorm : ∑ j,L j*R j=1 := by
    rw [← hd.normalized]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [L,R]
    field_simp [hdp.ne']
  have hsquare : ∑ j,R j^2=1 := by
    simp only [R,div_pow,← Finset.sum_div,hdsq]
    exact div_self hsum.ne'
  have hdata : PerronData A lam R L := by
    refine ⟨hd.eigenvalue_positive,fun j => div_pos (hd.right_positive j) hdp,
      fun j => mul_pos hdp (hd.left_positive j),hnorm,?_,?_,?_⟩
    · intro i
      simp only [R,← mul_div_assoc,← Finset.sum_div,hd.right_eigen]
    · intro j
      simp only [L,mul_assoc,← Finset.mul_sum,hd.left_eigen]
      ring
    · intro x hx
      have he := hd.simple x hx
      have hfun : complexFunctional L x=(d:ℂ)*complexFunctional l x := by
        simp only [complexFunctional_apply,L,Complex.ofReal_mul,mul_assoc,Finset.mul_sum]
      rw [hfun]
      funext j
      have hj := congrFun he j
      simp only [Pi.smul_apply,smul_eq_mul] at hj ⊢
      rw [show (R j:ℂ)=(r j:ℂ)/(d:ℂ) by simp [R]]
      have hdc : (d:ℂ)≠0 := by exact_mod_cast hdp.ne'
      rw [hj]
      field_simp
  refine ⟨hdata,hsquare,?_⟩
  have hsq : ‖(WithLp.toLp 2 R : EuclideanSpace ℝ (Fin n))‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ j,‖R j‖^2)=1
    simpa only [Real.norm_eq_abs,sq_abs] using hsquare
  nlinarith [norm_nonneg (WithLp.toLp 2 R : EuclideanSpace ℝ (Fin n))]

theorem normalize_perron_data {n : ℕ} (hn : 0<n)
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (r l : Fin n → ℝ)
    (hd : PerronData A lam r l) :
    ∃ R L : Fin n → ℝ,PerronData A lam R L ∧
      (∑ j,R j^2=1) ∧ ‖(WithLp.toLp 2 R : EuclideanSpace ℝ (Fin n))‖=1 := by
  exact ⟨_,_,normalized_perron_data_explicit hn A lam r l hd⟩

/-- At the actual regular frontier, ordinary Perron existence gives a
Euclidean-unit frame. Its eigenvalue-one conclusion is internal. -/
theorem normalized_frontier_perron
    (perron : ExternalPerronExistence) {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
    (hτ : τ∉Boundary.singularUnion m) :
    ∃ r l : Fin n → ℝ,PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) 1 r l ∧
      (∑ j,r j^2=1) ∧ ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖=1 := by
  obtain ⟨r,l,hr,hl,hpair,hFr,hlF,hsimple⟩ := regular_frontier_perron_data
    perron hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  apply normalize_perron_data hn _ 1 r l
  refine ⟨by norm_num,hr,hl,hpair,?_,?_,?_⟩
  · simpa using hFr
  · simpa using hlF
  · intro x hx
    exact hsimple x (by simpa using hx)

end NonSymmetricDyson.Paper.SingularitiesNormalization
