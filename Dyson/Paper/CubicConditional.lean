import Dyson.Paper.Cubic
import Dyson.Full.CubicUniform

/-! The cubic proposition under its own local nondegeneracy premise.
No (Sym) or (NB) assumption is imposed here. The exact actual Perron frame,
its complementary inverse, and the original coefficient lower bound are
inputs; Θ and every cubic coefficient use that same frame. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.CubicConditional
open Full Full.Singularities Full.PerronContinuation

theorem data_of_center_positive
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
    (hτ : τ∉Boundary.singularUnion m)
    (r l : Fin n → ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ))) 1 r l)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse
      (complexMatrixOperator (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)))).toLinearMap
      K.toLinearMap (complexFunctional l).toLinearMap (fun j => (r j:ℂ)))
    (hpositive : let p := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
      0<(quadraticCoefficient p l r)^2+
        cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) p l r
          (stableCoefficient p r K)) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
      D.p=(fun j => (Boundary.boundaryVector m (τ : ℂ) j).re/‖Boundary.boundaryVector m (τ : ℂ) j‖) ∧
      D.r=r ∧ D.l=l ∧ D.K=K.toLinearMap := by
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
  obtain ⟨u,huK,hul,hu⟩ := restricted_inverse_real_input (saturatedMatrix S m₀)
    r l K.toLinearMap hK hsimple (fun j => p j*r j^2)
  have huK' : K (fun j => (p j:ℂ)*(r j:ℂ)^2)=fun j => (u j:ℂ) := by
    simpa using huK
  have hueq : u=stableCoefficient p r K := by
    funext j
    have hh := congrArg Complex.re (congrFun huK' j)
    exact hh.symm
  have hu' : ∀ j,u j-∑ k,saturatedMatrix S m₀ j k*u k=
      p j*r j^2-r j*quadraticCoefficient p l r := by
    simpa [quadraticCoefficient,mul_assoc] using hu
  have hσ : complexFunctional l (fun j => (p j:ℂ)*(r j:ℂ)^2)=
      (quadraticCoefficient p l r:ℂ) := by
    simp [complexFunctional,quadraticCoefficient,Complex.ofReal_sum,
      Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]
  have hψ : complexFunctional l (fun j => (p j:ℂ)*(r j:ℂ)*
      (complexMatrixOperator (saturatedMatrix S m₀) (K (fun k => (p k:ℂ)*(r k:ℂ)^2)) j+
        K (fun k => (p k:ℂ)*(r k:ℂ)^2) j))=
      (cubicCoefficient (saturatedMatrix S m₀) p l r u:ℂ) := by
    rw [huK']
    simp [complexFunctional,complexMatrixOperator_apply,cubicCoefficient,
      Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_add,mul_add,add_comm,
      mul_left_comm,mul_comm,mul_assoc]
  have hpos : 0<(quadraticCoefficient p l r)^2+cubicCoefficient (saturatedMatrix S m₀) p l r u := by
    simpa only [hueq] using hpositive
  have hnondeg : quadraticCoefficient p l r≠0 ∨
      0<cubicCoefficient (saturatedMatrix S m₀) p l r u := by
    by_cases hz : quadraticCoefficient p l r=0
    · right
      simpa [hz] using hpos
    · exact Or.inl hz
  exact ⟨⟨p,r,l,u,K.toLinearMap,hreal,hnz,hp2,hpq,hr,hl,hnorm,hFr,hlF,hsimple,
    hK,huK',hul,hu',hσ,hψ,hnondeg⟩,rfl,rfl,rfl,rfl⟩


section Uniform
variable {n : ℕ} (hn : 0<n)
variable (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι:=Fin n))
variable (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
variable (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
variable (hS : Manuscript.PositivityCorrection.Nonnegative S)
variable (hirr : Manuscript.PositivityCorrection.Irreducible S)
variable (m : ℂ → Fin n → ℂ)
variable (hupper : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsUpperSolution (m z))
variable (heq : ∀ z∈ExternalAlgebraic.upper,BasicEstimates.IsDysonSolution S a z (m z))
variable (τ : ℝ) (i : Fin n) (hfront : τ∈frontier (Boundary.regularSupport m i))
variable (hτ : τ∉Boundary.singularUnion m)
variable (d : VaryingFrame S (Boundary.boundaryVector m)
  (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ)))
variable (hunit : ‖(WithLp.toLp 2 d.r₀ : EuclideanSpace ℝ (Fin n))‖=1)
variable (hbound : let p := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
  ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ),
    c≤(quadraticCoefficient p (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
        (stableCoefficient p (d.r z) (d.K z)) ∧
    (quadraticCoefficient p (d.l z) (d.r z))^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m z)) p (d.l z) (d.r z)
        (stableCoefficient p (d.r z) (d.K z))≤C)

include hn algebraic puiseux hS hirr hupper heq hfront hτ hbound hunit

/-- The literal local coefficient hypothesis gives center nondegeneracy
for the same prescribed Perron frame. No symmetry or graph condition is added. -/
theorem data_of_uniform_nondegeneracy :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ:ℂ)),
      D.p=(fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) ∧
      D.r=d.r₀ ∧ D.l=d.l₀ ∧ ‖(WithLp.toLp 2 D.r : EuclideanSpace ℝ (Fin n))‖=1 := by
  letI : Nonempty (Fin n) := ⟨i⟩
  letI : NeBot (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) :=
    nhdsWithin_neBot_of_mem (show (τ:ℂ)∈ExternalAlgebraic.closedUpper by
      change 0≤(τ:ℂ).im
      simp)
  let p : Fin n → ℝ := fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨K₀,hK₀,hKlim⟩ := d.inverse_limit hm
  have hu := stableCoefficient_tendsto p d.r d.K d.r₀ K₀ d.right_limit hKlim
  have hF := (saturatedMatrix_continuousAt S id (Boundary.boundaryVector m (τ:ℂ)) continuousAt_id).tendsto.comp hm
  obtain ⟨hσ,hψ⟩ := coefficient_tendsto _ p d.l d.r _ _ d.l₀ d.r₀ _
    hF d.left_limit d.right_limit hu
  obtain ⟨c,C,hc,_,hb⟩ := hbound
  have hpos : 0<(quadraticCoefficient p d.l₀ d.r₀)^2+
      cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) p d.l₀ d.r₀
        (stableCoefficient p d.r₀ K₀) :=
    hc.trans_le (ge_of_tendsto ((hσ.pow 2).add hψ) (hb.mono fun _ hz => hz.1))
  obtain ⟨D,hp,hr,hl,_⟩ := data_of_center_positive hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ d.r₀ d.l₀ d.center K₀ hK₀ hpos
  exact ⟨D,hp,hr,hl,by simpa only [hr] using hunit⟩

/-- The original conditional cubic proposition, for the exact normalized
frame occurring in its local coefficient premise. -/
theorem equation_of_uniform_nondegeneracy
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (imaginaryOrder : RealAnalyticImaginaryOrderBoundPrinciple) :
    ∃ D : FrontierData S (Boundary.boundaryVector m (τ:ℂ)),
    D.p=(fun j => (Boundary.boundaryVector m (τ:ℂ) j).re/‖Boundary.boundaryVector m (τ:ℂ) j‖) ∧
    D.r=d.r₀ ∧ D.l=d.l₀ ∧ ‖(WithLp.toLp 2 D.r : EuclideanSpace ℝ (Fin n))‖=1 ∧
    let m₀ := Boundary.boundaryVector m (τ : ℂ)
    let μ : ℝ := ∑ j, D.l j * ‖m₀ j‖
    let σ := quadraticCoefficient D.p D.l D.r
    let ψ := cubicCoefficient (saturatedMatrix S m₀) D.p D.l D.r D.u
    let Θ := boundaryCoordinate m τ D
    let e := fun x : ℝ => (μ : ℂ) * (x - τ : ℝ) + (σ : ℂ) * Θ x ^ 2 + (ψ : ℂ) * Θ x ^ 3
    0 < μ ∧ ∃ B > 0, ∀ᶠ x : ℝ in 𝓝 τ,
      0 ≤ (Θ x).im ∧
      (∀ j, ‖Boundary.boundaryVector m (x : ℂ) j - m₀ j -
        (‖m₀ j‖ : ℂ) * (D.r j : ℂ) * Θ x‖ ≤ B * (‖Θ x‖ ^ 2 + |x - τ|)) ∧
      ‖e x‖ ≤ B * (|x - τ| * ‖Θ x‖ + (x - τ) ^ 2) ∧
      |(e x).im| ≤ B * |x - τ| * (Θ x).im := by
  obtain ⟨D,hp,hr,hl,hu⟩ := data_of_uniform_nondegeneracy hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ d hunit hbound
  exact ⟨D,hp,hr,hl,hu,Cubic.equation_with_perron_data normalForm imaginaryOrder hn
    algebraic puiseux S a hS m hupper heq τ hτ D⟩

/-- The genuine two-point 1/3-Hölder clause on the closed upper neighborhood,
under exactly the same conditional coefficient assumption. -/
theorem holder_of_uniform_nondegeneracy
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple) :
    ∃ C ε : ℝ,0<C ∧ 0<ε ∧
      ∀ z∈ExternalAlgebraic.closedUpper,∀ w∈ExternalAlgebraic.closedUpper,
        ‖z-(τ:ℂ)‖<ε → ‖w-(τ:ℂ)‖<ε →
        ‖Boundary.boundaryVector m z-Boundary.boundaryVector m w‖≤C*‖z-w‖^((1:ℝ)/3) := by
  obtain ⟨D,_,_,_,_⟩ := data_of_uniform_nondegeneracy hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ d hunit hbound
  exact Cubic.holder_with_perron_data normalForm orientation hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ D

end Uniform

end NonSymmetricDyson.Paper.CubicConditional
