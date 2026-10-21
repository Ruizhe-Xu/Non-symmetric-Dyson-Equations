import Dyson.Full.PerronVarying
import Dyson.Full.RestrictedInverseLimit
import Dyson.Full.CubicPositivity
import Dyson.Full.PerronStable
import Dyson.Full.PerronSpectrum

/-! Continuity of the actual cubic coefficients and uniform nondegeneracy
near a regular frontier. No continuity of an inverse is assumed. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.PerronContinuation
open Singularities
variable {X : Type*} {n : ℕ} [Nonempty (Fin n)]

def stableCoefficient (p r : Fin n → ℝ)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (i : Fin n) : ℝ :=
  (K (fun j => (p j:ℂ)*(r j:ℂ)^2) i).re

theorem stableCoefficient_identities (F : Matrix (Fin n) (Fin n) ℝ)
    (p r l : Fin n → ℝ) (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ))) :
    (∑ i,l i*stableCoefficient p r K i=0) ∧
    ∀ i,stableCoefficient p r K i-∑ j,F i j*stableCoefficient p r K j=
      p i*r i^2-r i*quadraticCoefficient p l r := by
  constructor
  · have hh := congrArg Complex.re (hK.kill_left (fun j => (p j:ℂ)*(r j:ℂ)^2))
    simpa [complexFunctional,stableCoefficient,Complex.mul_re] using hh
  · intro i
    have hh := congrArg Complex.re
      (congrFun (hK.right_inverse (fun j => (p j:ℂ)*(r j:ℂ)^2)) i)
    simpa [complexMatrixOperator_apply,complexFunctional,stableCoefficient,
      quadraticCoefficient,← Complex.ofReal_pow,Complex.mul_re,mul_comm,mul_left_comm,mul_assoc] using hh

theorem VaryingFrame.inverse_limit {S : Matrix (Fin n) (Fin n) ℝ}
    {m : X → Fin n → ℂ} {L : Filter X} {m₀ : Fin n → ℂ}
    (d : VaryingFrame S m L m₀) (hm : Tendsto m L (𝓝 m₀)) :
    ∃ K₀ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
      IsRestrictedInverse (complexMatrixOperator (saturatedMatrix S m₀)).toLinearMap K₀.toLinearMap
        (complexFunctional d.l₀).toLinearMap (fun i => (d.r₀ i:ℂ)) ∧
      Tendsto d.K L (𝓝 K₀) := by
  let F₀ := complexMatrixOperator (saturatedMatrix S m₀)
  let φ₀ := complexFunctional d.l₀
  let r₀ : Fin n → ℂ := fun i => (d.r₀ i:ℂ)
  have hn : φ₀ r₀=1 := by
    change complexFunctional d.l₀ r₀=1
    rw [complexFunctional_apply]
    dsimp [r₀]
    exact_mod_cast d.center.normalized
  have hr : F₀ r₀=r₀ := by
    funext i
    change (∑ j,((saturatedMatrix S m₀) i j:ℂ)*(d.r₀ j:ℂ))=(d.r₀ i:ℂ)
    exact_mod_cast (by simpa using d.center.right_eigen i)
  have hl : ∀ x,φ₀ (F₀ x)=φ₀ x := by
    intro x
    change complexFunctional d.l₀ (complexMatrixOperator (saturatedMatrix S m₀) x)=complexFunctional d.l₀ x
    simpa only [Complex.ofReal_one,one_mul] using functional_left_eigen _ _ _ d.center.left_eigen x
  have hs : ∀ x,F₀ x=x → x=φ₀ x • r₀ := fun x hx => d.center.simple x (by simpa using hx)
  obtain ⟨K,hK⟩ := restricted_inverse_exists F₀.toLinearMap φ₀.toLinearMap r₀ hn hr hl hs
  let K₀ := K.toContinuousLinearMap
  have hK₀ : IsRestrictedInverse F₀.toLinearMap K₀.toLinearMap φ₀.toLinearMap r₀ := hK
  refine ⟨K₀,hK₀,?_⟩
  have hF := (saturatedMatrix_continuousAt S id m₀ continuousAt_id).tendsto.comp hm
  have hFc := matrixOperator_continuous.continuousAt.tendsto.comp hF
  have hφ := functional_continuous.continuousAt.tendsto.comp d.left_limit
  have hrc : Tendsto (fun x i => (d.r x i:ℂ)) L (𝓝 r₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_pi_nhds.mp d.right_limit) i)
  obtain ⟨B,b,hB,_,hb⟩ := d.uniform
  have hKb : ∀ᶠ x in L, ‖d.K x‖≤B := hb.mono (fun _ h => h.2.2.1)
  exact RestrictedInverseUniform.restricted_inverse_tendsto L
    (fun x => complexMatrixOperator (saturatedMatrix S (m x))) d.K
    (fun x => complexFunctional (d.l x)) (fun x i => (d.r x i:ℂ))
    F₀ K₀ φ₀ r₀ hFc hφ hrc hK₀ d.restricted B hB.le hKb

theorem stableCoefficient_tendsto {L : Filter X}
    (p : Fin n → ℝ) (r : X → Fin n → ℝ)
    (K : X → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (r₀ : Fin n → ℝ) (K₀ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hr : Tendsto r L (𝓝 r₀)) (hK : Tendsto K L (𝓝 K₀)) :
    Tendsto (fun x => stableCoefficient p (r x) (K x)) L
      (𝓝 (stableCoefficient p r₀ K₀)) := by
  have hv : Tendsto (fun x i => (p i:ℂ)*(r x i:ℂ)^2) L
      (𝓝 (fun i => (p i:ℂ)*(r₀ i:ℂ)^2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_pi_nhds.mp hr) i)).pow 2)
  have hx := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hK.prodMk_nhds hv)
  apply tendsto_pi_nhds.mpr
  intro i
  exact Complex.continuous_re.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hx) i)

theorem coefficient_tendsto {L : Filter X}
    (F : X → Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (l r u : X → Fin n → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (l₀ r₀ u₀ : Fin n → ℝ)
    (hF : Tendsto F L (𝓝 F₀)) (hl : Tendsto l L (𝓝 l₀))
    (hr : Tendsto r L (𝓝 r₀)) (hu : Tendsto u L (𝓝 u₀)) :
    Tendsto (fun x => quadraticCoefficient p (l x) (r x)) L (𝓝 (quadraticCoefficient p l₀ r₀)) ∧
    Tendsto (fun x => cubicCoefficient (F x) p (l x) (r x) (u x)) L
      (𝓝 (cubicCoefficient F₀ p l₀ r₀ u₀)) := by
  constructor
  · apply tendsto_finset_sum
    intro i _
    exact (((tendsto_pi_nhds.mp hl) i).mul_const (p i)).mul
      (((tendsto_pi_nhds.mp hr) i).pow 2)
  · apply tendsto_finset_sum
    intro i _
    apply ((tendsto_const_nhds.mul ((tendsto_pi_nhds.mp hl) i)).mul
      ((tendsto_pi_nhds.mp hr) i)).mul
    apply ((tendsto_pi_nhds.mp hu) i).add
    apply tendsto_finset_sum
    intro j _
    exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hF) i)) j).mul ((tendsto_pi_nhds.mp hu) j)

/-- Strict nondegeneracy at the center propagates uniformly to a moving
Perron frame, with the stable inverse and coefficients constructed internally. -/
theorem VaryingFrame.uniform_nondegeneracy {S : Matrix (Fin n) (Fin n) ℝ}
    {m : X → Fin n → ℂ} {L : Filter X} {m₀ : Fin n → ℂ}
    (d : VaryingFrame S m L m₀) (hm : Tendsto m L (𝓝 m₀)) (p : Fin n → ℝ)
    (hnon : ∀ u : Fin n → ℝ, (∑ i,d.l₀ i*u i=0) →
      (∀ i,u i-∑ j,saturatedMatrix S m₀ i j*u j=
        p i*d.r₀ i^2-d.r₀ i*quadraticCoefficient p d.l₀ d.r₀) →
      0<(quadraticCoefficient p d.l₀ d.r₀)^2+
        cubicCoefficient (saturatedMatrix S m₀) p d.l₀ d.r₀ u) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ x in L,
      c≤(quadraticCoefficient p (d.l x) (d.r x))^2+
        cubicCoefficient (saturatedMatrix S (m x)) p (d.l x) (d.r x)
          (stableCoefficient p (d.r x) (d.K x)) ∧
      (quadraticCoefficient p (d.l x) (d.r x))^2+
        cubicCoefficient (saturatedMatrix S (m x)) p (d.l x) (d.r x)
          (stableCoefficient p (d.r x) (d.K x))≤C := by
  obtain ⟨K₀,hK₀,hKlim⟩ := d.inverse_limit hm
  have hu := stableCoefficient_tendsto p d.r d.K d.r₀ K₀ d.right_limit hKlim
  have hF := (saturatedMatrix_continuousAt S id m₀ continuousAt_id).tendsto.comp hm
  obtain ⟨hσ,hψ⟩ := coefficient_tendsto _ p d.l d.r _ _ d.l₀ d.r₀ _
    hF d.left_limit d.right_limit hu
  have hids := stableCoefficient_identities _ p d.r₀ d.l₀ K₀ hK₀
  have hpositive := hnon _ hids.1 hids.2
  let v : ℝ := (quadraticCoefficient p d.l₀ d.r₀)^2+
    cubicCoefficient (saturatedMatrix S m₀) p d.l₀ d.r₀ (stableCoefficient p d.r₀ K₀)
  have hv : 0<v := hpositive
  have hlim := (hσ.pow 2).add hψ
  refine ⟨v/2,v+1,by positivity,by positivity,?_⟩
  exact (hlim.eventually_const_le (show v/2<v by linarith)).and
    (hlim.eventually_le_const (show v<v+1 by linarith))

/-- Actual upper-half-plane ψ positivity, using the exact Perron eigenvalue
identity derived from the imaginary Dyson equation. -/
theorem actual_cubic_positive_upper
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (z : ℂ) (m : Fin n → ℂ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (p r l : Fin n → ℝ) (lam : ℝ)
    (hd : PerronData (saturatedMatrix S m) lam r l)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse (complexMatrixOperator (saturatedMatrix S m)).toLinearMap
      K.toLinearMap (complexFunctional l).toLinearMap (fun i => (r i:ℂ))) :
    0≤cubicCoefficient (saturatedMatrix S m) p l r (stableCoefficient p r K) := by
  have hlam := perron_eigenvalue_lt_one S a z m hz hm heq l lam hd.left_positive hd.left_eigen
  obtain ⟨ho,hu⟩ := stableCoefficient_identities _ p r l K hK
  exact cubicCoefficient_nonnegative_projected _ p l r _ lam (quadraticCoefficient p l r)
    (saturatedMatrix_nonnegative S hS m) hd.left_positive hd.right_positive
    hd.eigenvalue_positive hlam.le hd.right_eigen hd.left_eigen ho
    (by simpa [mul_comm] using hu)

/-- Nondegeneracy and ψ≥0 hold for the actual frontier and every normalized
positive Perron frame there. No specially chosen normalization is assumed. -/
theorem regular_frontier_coefficient_positive
    (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
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
  let m₀ : Fin n → ℂ := Boundary.boundaryVector m (τ : ℂ)
  let b : Fin n → ℝ := fun j => (m₀ j).re
  let q : Fin n → ℝ := fun j => ‖m₀ j‖
  let p : Fin n → ℝ := fun j => b j / q j
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
  have hsimple : ∀ x:Fin n → ℂ,complexMatrixOperator (saturatedMatrix S m₀) x=x →
      x=complexFunctional l x • (fun j => (r j:ℂ)) := fun x hx => hd.simple x (by simpa using hx)
  obtain ⟨E, hE, _, hpos, hsol, hlim⟩ :=
    Boundary.regular_frontier_sequence hn algebraic puiseux S a hS hirr m hupper heq
      τ i hfront hτ
  let w : ℕ → ℂ := fun k => (E k : ℂ) - (τ : ℂ)
  let g : ℕ → Fin n → ℂ := fun k => Boundary.boundaryVector m (E k : ℂ)
  have hbase : PolynomialDyson.IsPolynomialSolution S a (τ : ℂ) (fun j => (b j : ℂ)) := by
    rw [hcast]
    exact PolynomialDyson.of_dyson hboundary.2.2 hnz
  have hphysical (k : ℕ) : PolynomialDyson.IsPolynomialSolution S a ((τ : ℂ) + w k) (g k) := by
    have henergy : (τ : ℂ) + w k = (E k : ℂ) := by dsimp [w]; ring
    rw [henergy]
    exact PolynomialDyson.of_dyson (hsol k) (BasicEstimates.component_ne_zero (hpos k))
  have hwlim : Tendsto w atTop (𝓝 (0 : ℂ)) := by
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hE).sub_const (τ : ℂ)
    simpa [w] using hh
  have hconv : Tendsto (fun k => (w k, g k)) atTop
      (𝓝 (0, fun j => (b j : ℂ))) := by
    rw [hcast]
    exact hwlim.prodMk_nhds hlim
  have hw (k : ℕ) : w k ≠ 0 := by
    intro hk
    have hEt : E k = τ := Complex.ofReal_injective (sub_eq_zero.mp hk)
    have hh := hpos k i
    rw [hEt] at hh
    exact (ne_of_gt hh) (hreal i)
  have hnondeg := singularity_coefficients_nondegenerate S (saturatedMatrix S m₀) a (τ:ℂ)
    b p q r l u hS hp2 hpq hqpos hd.right_positive hd.left_positive (fun _ _ => rfl)
    hFr hlF hd.normalized hsimple hu hbase w g hphysical hconv hw
  have hψ := cubicCoefficient_nonnegative_projected (saturatedMatrix S m₀) p l r u 1
    (quadraticCoefficient p l r) (saturatedMatrix_nonnegative S hS m₀)
    hd.left_positive hd.right_positive (by norm_num) (by norm_num)
    hd.right_eigen hd.left_eigen horth (by simpa [mul_comm] using hu)
  rcases hnondeg with hσ | hposψ
  · have hs : 0<(quadraticCoefficient p l r)^2 := sq_pos_of_ne_zero hσ
    exact add_pos_of_pos_of_nonneg hs hψ
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) hposψ

/-- The manuscript's uniform σ²+ψ≍1 on the full closed upper neighborhood
is now a theorem about the actual solution and its constructed Perron frame. -/
theorem regular_frontier_uniform_nondegeneracy
    (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
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
  dsimp only
  apply d.uniform_nondegeneracy (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
  intro u ho hu
  exact regular_frontier_coefficient_positive hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ d.r₀ d.l₀ u d.center ho hu

/-- ψ≥0 also at every regular real boundary point, including gaps. -/
theorem actual_cubic_positive_boundary
    (external : ExternalContinuousPerron) (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m)
    (p r l : Fin n → ℝ) (lam : ℝ)
    (hd : PerronData (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ))) lam r l)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse
      (complexMatrixOperator (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)))).toLinearMap
      K.toLinearMap (complexFunctional l).toLinearMap (fun i => (r i:ℂ))) :
    0≤cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ:ℂ)))
      p l r (stableCoefficient p r K) := by
  have hlam := regular_boundary_perron_le_one external hn algebraic puiseux S a hS hirr
    m hupper heq τ hτ l lam hd.left_positive hd.left_eigen
  obtain ⟨ho,hu⟩ := stableCoefficient_identities _ p r l K hK
  exact cubicCoefficient_nonnegative_projected _ p l r _ lam (quadraticCoefficient p l r)
    (saturatedMatrix_nonnegative S hS _) hd.left_positive hd.right_positive
    hd.eigenvalue_positive hlam hd.right_eigen hd.left_eigen ho (by simpa [mul_comm] using hu)

end NonSymmetricDyson.Full.PerronContinuation
