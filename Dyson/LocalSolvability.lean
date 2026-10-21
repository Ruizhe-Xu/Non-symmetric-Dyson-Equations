import Mathlib
import Dyson.Model
import Dyson.InteriorStability
import Dyson.Uniqueness

/-!
# Local solvability of the vector Dyson equation

The polynomial map used below is genuinely differentiated. Its derivative is
shown invertible from interior linear stability, and the inverse function
theorem then produces local upper-half-plane solutions.
-/

noncomputable section
open scoped Topology BigOperators
open Filter

namespace NonSymmetricDyson.LocalSolvability

variable {ι : Type*} [Fintype ι]

abbrev Augmented := ℂ × (ι → ℂ)

def coordinate (i : ι) : Augmented (ι := ι) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))

def innerLinear (S : Matrix ι ι ℝ) (i : ι) : Augmented (ι := ι) →L[ℂ] ℂ :=
  ContinuousLinearMap.fst ℂ ℂ (ι → ℂ) +
    ∑ j, (S i j : ℂ) • coordinate j

omit [Fintype ι] in
@[simp] theorem coordinate_apply (i : ι) (p : Augmented (ι := ι)) :
    coordinate i p = p.2 i := rfl

@[simp] theorem innerLinear_apply (S : Matrix ι ι ℝ) (i : ι)
    (p : Augmented (ι := ι)) :
    innerLinear S i p = p.1 + ∑ j, (S i j : ℂ) * p.2 j := by
  simp [innerLinear, coordinate]

/-- Clearing denominators gives the actual polynomial residual. -/
def polynomialResidual (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) : ι → ℂ :=
  fun i => 1 + p.2 i * (innerLinear S i p - (a i : ℂ))

def totalMap (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) : Augmented (ι := ι) :=
  (p.1, polynomialResidual S a p)

/-- Explicit Fréchet derivative of the polynomial residual. -/
def residualDerivative (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) : Augmented (ι := ι) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (p.2 i) • innerLinear S i + (innerLinear S i p - (a i : ℂ)) • coordinate i

def totalDerivative (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) :
    Augmented (ι := ι) →L[ℂ] Augmented (ι := ι) :=
  (ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).prod (residualDerivative S a p)

@[simp] theorem residualDerivative_apply (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p v : Augmented (ι := ι)) (i : ι) :
    residualDerivative S a p v i =
      p.2 i * (v.1 + ∑ j, (S i j : ℂ) * v.2 j) +
        (p.1 + ∑ j, (S i j : ℂ) * p.2 j - (a i : ℂ)) * v.2 i := by
  simp [residualDerivative]

@[simp] theorem totalDerivative_fst (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p v : Augmented (ι := ι)) : (totalDerivative S a p v).1 = v.1 := rfl

@[simp] theorem totalDerivative_snd (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p v : Augmented (ι := ι)) :
    (totalDerivative S a p v).2 = residualDerivative S a p v := rfl

theorem polynomialResidual_hasStrictFDerivAt (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) :
    HasStrictFDerivAt (polynomialResidual S a) (residualDerivative S a p) p := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  have hc := (coordinate (ι := ι) i).hasStrictFDerivAt (x := p)
  have hl := ((innerLinear S i).hasStrictFDerivAt (x := p)).sub_const (a i : ℂ)
  exact (hc.fun_mul hl).const_add 1

theorem totalMap_hasStrictFDerivAt (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) :
    HasStrictFDerivAt (totalMap S a) (totalDerivative S a p) p :=
  hasStrictFDerivAt_fst.prodMk (polynomialResidual_hasStrictFDerivAt S a p)

/-- For nonzero coordinates, polynomial residual zero is equivalent to the
original reciprocal equation, with precisely the manuscript's sign. -/
theorem polynomialResidual_zero_iff (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z : ℂ) (m : ι → ℂ) (hm0 : ∀ i, m i ≠ 0) :
    polynomialResidual S a (z, m) = 0 ↔ BasicEstimates.IsDysonSolution S a z m := by
  constructor
  · intro h i
    have hi := congrFun h i
    simp only [polynomialResidual, innerLinear_apply, Pi.zero_apply] at hi
    apply (mul_left_cancel₀ (hm0 i))
    have hn := mul_inv_cancel₀ (hm0 i)
    simp only [mul_neg, hn]
    linear_combination -hi
  · intro h
    ext i
    have hi := h i
    simp only [polynomialResidual, innerLinear_apply, Pi.zero_apply]
    rw [show z + ∑ j, (S i j : ℂ) * m j - (a i : ℂ) =
      -(m i)⁻¹ by linear_combination -hi]
    simp [hm0 i]


/-- The derivative is bijective at every genuine upper-half-plane solution.
This conclusion uses interior stability, not an assumed inverse derivative. -/
theorem totalDerivative_bijective (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z.im)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m) :
    Function.Bijective (totalDerivative S a (z, m)) := by
  have hinj : Function.Injective
      (totalDerivative S a (z, m)).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hv₁ : v.1 = 0 := congrArg Prod.fst hv
    have hv₂ : InteriorStability.stabilityOperator S m v.2 = 0 := by
      ext i
      have hi := congrFun (congrArg Prod.snd hv) i
      change residualDerivative S a (z, m) v i = 0 at hi
      have hinner : z + ∑ j, (S i j : ℂ) * m j - (a i : ℂ) = -(m i)⁻¹ := by
        have hs := hsol i
        linear_combination -hs
      simp only [residualDerivative_apply, hv₁, zero_add, hinner] at hi
      simp only [InteriorStability.stabilityOperator_apply, Pi.zero_apply]
      have hm0 := BasicEstimates.component_ne_zero hm i
      field_simp [hm0] at hi
      linear_combination -hi
    have hvm : v.2 = 0 :=
      (InteriorStability.stability_bijective hS hz hm hsol).1
        (by simpa using hv₂)
    exact Prod.ext hv₁ hvm
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩


/-- The augmented residual is a genuinely complex-analytic polynomial map. -/
theorem totalMap_analyticAt (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (p : Augmented (ι := ι)) : AnalyticAt ℂ (totalMap S a) p := by
  apply ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt p).prod
  apply AnalyticAt.pi
  intro i
  exact analyticAt_const.add (((coordinate (ι := ι) i).analyticAt p).fun_mul
    (((innerLinear S i).analyticAt p).sub analyticAt_const))

/-- Near an actual interior solution there is a complex-analytic branch of
upper-half-plane solutions. All inverse-function hypotheses are proved here. -/
theorem exists_analytic_local_branch (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z₀ : ℂ) (m₀ : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z₀.im)
    (hm : BasicEstimates.IsUpperSolution m₀)
    (hsol : BasicEstimates.IsDysonSolution S a z₀ m₀) :
    ∃ branch : ℂ → (ι → ℂ), AnalyticAt ℂ branch z₀ ∧ branch z₀ = m₀ ∧
      ∀ᶠ z in 𝓝 z₀,
        BasicEstimates.IsUpperSolution (branch z) ∧
          BasicEstimates.IsDysonSolution S a z (branch z) := by
  have hmzero := (polynomialResidual_zero_iff S a z₀ m₀
    (BasicEstimates.component_ne_zero hm)).mpr hsol
  have hpoint : totalMap S a (z₀, m₀) = (z₀, 0) := Prod.ext rfl hmzero
  have hb := totalDerivative_bijective S a z₀ m₀ hS hz hm hsol
  let e := ContinuousLinearEquiv.ofBijective (totalDerivative S a (z₀, m₀))
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hder : HasStrictFDerivAt (totalMap S a) (e :
      Augmented (ι := ι) →L[ℂ] Augmented (ι := ι)) (z₀, m₀) :=
    totalMap_hasStrictFDerivAt S a (z₀, m₀)
  let inv := hder.localInverse (totalMap S a) e (z₀, m₀)
  have hinvAnalytic : AnalyticAt ℂ inv (totalMap S a (z₀, m₀)) :=
    (hder.toOpenPartialHomeomorph (totalMap S a)).analyticAt_symm'
      hder.mem_toOpenPartialHomeomorph_source (totalMap_analyticAt S a (z₀, m₀))
      hder.hasFDerivAt.fderiv
  have hembed : Tendsto (fun z : ℂ => (z, (0 : ι → ℂ)))
      (𝓝 z₀) (𝓝 (totalMap S a (z₀, m₀))) := by
    rw [hpoint]
    exact continuousAt_id.prodMk continuousAt_const
  have hbranchAnalytic : AnalyticAt ℂ (fun z : ℂ => (inv (z, 0)).2) z₀ := by
    have hi : AnalyticAt ℂ inv (z₀, 0) := by simpa only [hpoint] using hinvAnalytic
    have hembedAnalytic : AnalyticAt ℂ (fun z : ℂ => (z, (0 : ι → ℂ))) z₀ :=
      analyticAt_id.prod analyticAt_const
    exact ((ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)).analyticAt _).comp
      (hi.comp (f := fun z : ℂ => (z, (0 : ι → ℂ))) hembedAnalytic)
  have hinvPoint : inv (z₀, 0) = (z₀, m₀) := by
    simpa only [hpoint] using hder.localInverse_apply_image
  have hupper : ∀ᶠ p : Augmented (ι := ι) in 𝓝 (z₀, m₀),
      BasicEstimates.IsUpperSolution p.2 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd))).mem_nhds
        (hm i)
  have hupperInv : ∀ᶠ z in 𝓝 z₀, BasicEstimates.IsUpperSolution (inv (z, 0)).2 :=
    (hder.localInverse_tendsto.comp hembed).eventually hupper
  have hright : ∀ᶠ z in 𝓝 z₀, totalMap S a (inv (z, 0)) = (z, 0) :=
    hembed.eventually hder.eventually_right_inverse
  refine ⟨fun z => (inv (z, 0)).2, hbranchAnalytic, congrArg Prod.snd hinvPoint, ?_⟩
  filter_upwards [hupperInv, hright] with z hu hr
  refine ⟨hu, ?_⟩
  have hzfirst : (inv (z, 0)).1 = z := congrArg Prod.fst hr
  have hzres : polynomialResidual S a (inv (z, 0)) = 0 := congrArg Prod.snd hr
  have hzpair : inv (z, 0) = (z, (inv (z, 0)).2) := Prod.ext hzfirst rfl
  rw [hzpair] at hzres
  exact (polynomialResidual_zero_iff S a z (inv (z, 0)).2
    (BasicEstimates.component_ne_zero hu)).mp hzres

/-- Solvability persists in an actual neighborhood of every existing interior
solution. No implicit solution or differentiability hypothesis is assumed. -/
theorem local_solvability (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (z₀ : ℂ) (m₀ : ι → ℂ)
    (hS : ∀ i j, 0 ≤ S i j) (hz : 0 < z₀.im)
    (hm : BasicEstimates.IsUpperSolution m₀)
    (hsol : BasicEstimates.IsDysonSolution S a z₀ m₀) :
    ∀ᶠ z in 𝓝 z₀, ∃ m : ι → ℂ,
      BasicEstimates.IsUpperSolution m ∧ BasicEstimates.IsDysonSolution S a z m := by
  have hmzero := (polynomialResidual_zero_iff S a z₀ m₀
    (BasicEstimates.component_ne_zero hm)).mpr hsol
  have hpoint : totalMap S a (z₀, m₀) = (z₀, 0) := Prod.ext rfl hmzero
  have hb := totalDerivative_bijective S a z₀ m₀ hS hz hm hsol
  have hmap := (totalMap_hasStrictFDerivAt S a (z₀, m₀)).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hb.2)
  have hupper : ∀ᶠ p : Augmented (ι := ι) in 𝓝 (z₀, m₀),
      BasicEstimates.IsUpperSolution p.2 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (isOpen_lt continuous_const
      (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd))).mem_nhds
        (hm i)
  have himage : ∀ᶠ q in 𝓝 (totalMap S a (z₀, m₀)),
      ∃ p : Augmented (ι := ι), BasicEstimates.IsUpperSolution p.2 ∧
        totalMap S a p = q := by
    rw [← hmap]
    change ∀ᶠ p in 𝓝 (z₀, m₀),
      ∃ q : Augmented (ι := ι), BasicEstimates.IsUpperSolution q.2 ∧
        totalMap S a q = totalMap S a p
    exact hupper.mono fun p hp => ⟨p, hp, rfl⟩
  have hembed : Tendsto (fun z : ℂ => (z, (0 : ι → ℂ)))
      (𝓝 z₀) (𝓝 (totalMap S a (z₀, m₀))) := by
    rw [hpoint]
    exact continuousAt_id.prodMk continuousAt_const
  filter_upwards [hembed.eventually himage] with z hz
  obtain ⟨p, hp, heq⟩ := hz
  have hpz : p.1 = z := congrArg Prod.fst heq
  have hpR : polynomialResidual S a p = 0 := congrArg Prod.snd heq
  have hpair : p = (z, p.2) := Prod.ext hpz rfl
  rw [hpair] at hpR
  exact ⟨p.2, hp, (polynomialResidual_zero_iff S a z p.2
    (BasicEstimates.component_ne_zero hp)).mp hpR⟩

/-- The set of solvable parameters is open relative to the upper half-plane. -/
theorem isOpen_solvable_upper (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) :
    IsOpen {z : {z : ℂ // 0 < z.im} | ∃ m : ι → ℂ,
      BasicEstimates.IsUpperSolution m ∧ BasicEstimates.IsDysonSolution S a z.val m} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨m, hm, hsol⟩ := hz
  exact continuous_subtype_val.continuousAt
    (local_solvability S a z.val m hS z.property hm hsol)


/-- Every family of genuine upper-half-plane Dyson solutions is analytic.
No continuity, differentiability, or local existence assumption is made on the
family: the local analytic inverse branch and proved uniqueness imply it. -/
theorem analyticAt_of_solution_family (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (f : ℂ → (ι → ℂ)) (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (f z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (f z))
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) : AnalyticAt ℂ f z₀ := by
  obtain ⟨branch, hb, _hb₀, hevent⟩ :=
    exists_analytic_local_branch S a z₀ (f z₀) hS hz₀ (hupper z₀ hz₀) (hsol z₀ hz₀)
  have hparameter : ∀ᶠ z : ℂ in 𝓝 z₀, 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀
  apply hb.congr
  filter_upwards [hevent, hparameter] with z hbz hz
  exact Uniqueness.upper_half_plane_unique hS hz hbz.1 (hupper z hz) hbz.2 (hsol z hz)

/-- The analytic dependence part of the paper's first main theorem, for any
chosen solution family. The matrix need not be symmetric or irreducible. -/
theorem analyticOnNhd_of_solution_family (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (f : ℂ → (ι → ℂ)) (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (f z))
    (hsol : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S a z (f z)) :
    AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} :=
  fun _ hz => analyticAt_of_solution_family S a f hS hupper hsol hz

end NonSymmetricDyson.LocalSolvability
