import Dyson.Full.PerronContinuation
import Dyson.Full.BoundaryLocalLimits

/-! The actual moving Perron frame, on an arbitrary approach filter.
All complementary inverses and all uniform bounds are constructed from the
finite-dimensional Perron chart and the actual limiting saturated matrix. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.PerronContinuation
open Singularities

structure VaryingFrame {X : Type*} {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (m : X → Fin n → ℂ)
    (L : Filter X) (m₀ : Fin n → ℂ) where
  lam : X → ℝ
  r : X → Fin n → ℝ
  l : X → Fin n → ℝ
  K : X → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)
  r₀ : Fin n → ℝ
  l₀ : Fin n → ℝ
  center : PerronData (saturatedMatrix S m₀) 1 r₀ l₀
  lam_limit : Tendsto lam L (𝓝 1)
  right_limit : Tendsto r L (𝓝 r₀)
  left_limit : Tendsto l L (𝓝 l₀)
  nearby : ∀ᶠ x in L, PerronData (saturatedMatrix S (m x)) (lam x) (r x) (l x)
  restricted : ∀ᶠ x in L, IsRestrictedInverse
    (complexMatrixOperator (saturatedMatrix S (m x))).toLinearMap (K x).toLinearMap
    (complexFunctional (l x)).toLinearMap (fun i => (r x i:ℂ))
  real_preserving : ∀ᶠ x in L, ∀ b : Fin n → ℝ, ∃ u : Fin n → ℝ,
    K x (fun i => (b i:ℂ))=fun i => (u i:ℂ)
  uniform : ∃ B b : ℝ, 0<B ∧ 0<b ∧ ∀ᶠ x in L,
    ‖(fun i => (r x i:ℂ))‖≤B ∧ ‖complexFunctional (l x)‖≤B ∧ ‖K x‖≤B ∧
    ‖(fun i => (‖m x i‖:ℂ))‖≤B ∧
    ‖K x (fun i => (‖m x i‖:ℂ))‖≤B ∧ ∀ i, b≤l x i

theorem restricted_inverse_real_of_complement {n : ℕ} [Nonempty (Fin n)]
    (F : Matrix (Fin n) (Fin n) ℝ) (r l : Fin n → ℝ)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ)))
    (hkernel : ∀ x, complexFunctional l x=0 → complexMatrixOperator F x=x → x=0)
    (b : Fin n → ℝ) : ∃ u : Fin n → ℝ, K (fun i => (b i:ℂ))=fun i => (u i:ℂ) := by
  let x : Fin n → ℂ := K (fun i => (b i:ℂ))
  let v : Fin n → ℝ := fun i => (x i).im
  have hright : x-complexMatrixOperator F x=(fun i => (b i:ℂ))-
      complexFunctional l (fun i => (b i:ℂ)) • (fun i => (r i:ℂ)) := hK.right_inverse _
  have hleft : complexFunctional l x=0 := hK.kill_left _
  have hvi (i : Fin n) : v i-∑ j,F i j*v j=0 := by
    have h := congrArg Complex.im (congrFun hright i)
    simpa [complexMatrixOperator_apply,complexFunctional,Complex.mul_im,v] using h
  have hvleft : ∑ i,l i*v i=0 := by
    have h := congrArg Complex.im hleft
    simpa [complexFunctional,Complex.mul_im,v] using h
  have hvfixed : complexMatrixOperator F (fun i => (v i:ℂ))=fun i => (v i:ℂ) := by
    funext i
    change (∑ j,(F i j:ℂ)*(v j:ℂ))=(v i:ℂ)
    exact_mod_cast (sub_eq_zero.mp (hvi i)).symm
  have hvfunctional : complexFunctional l (fun i => (v i:ℂ))=0 := by
    rw [complexFunctional_apply]
    exact_mod_cast hvleft
  have hvzero := hkernel _ hvfunctional hvfixed
  refine ⟨fun i => (x i).re,?_⟩
  funext i
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.re (congrFun hvzero i)
    simpa [v] using h

/-- The generic Perron chart yields a bounded real complementary inverse
along any family converging to a simple Perron eigenvalue one. -/
theorem varying_frame_exists (external : ExternalContinuousPerron)
    {X : Type*} {n : ℕ} (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : X → Fin n → ℂ) (L : Filter X) (m₀ : Fin n → ℂ)
    (hm : Tendsto m L (𝓝 m₀)) (hnz : ∀ i,m₀ i≠0)
    (hone : ∀ lam r l, PerronData (saturatedMatrix S m₀) lam r l → lam=1) :
    Nonempty (VaryingFrame S m L m₀) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let F₀ := saturatedMatrix S m₀
  obtain ⟨U,hU,hmem,lam,r,l,hla,hr,hl,hdata⟩ := external n hn F₀
    (saturatedMatrix_nonnegative S hS _) (saturatedMatrix_irreducible S hS hirr _ hnz)
  have hbase := hdata F₀ hmem
  have hlam₀ : lam F₀=1 := hone _ _ _ hbase
  let F : X → Matrix (Fin n) (Fin n) ℝ := fun x => saturatedMatrix S (m x)
  have hF : Tendsto F L (𝓝 F₀) :=
    (saturatedMatrix_continuousAt S id m₀ continuousAt_id).tendsto.comp hm
  have hlam : Tendsto (fun x => lam (F x)) L (𝓝 1) := by
    rw [← hlam₀]
    exact (hla.continuousAt (hU.mem_nhds hmem)).tendsto.comp hF
  have hright : Tendsto (fun x => r (F x)) L (𝓝 (r F₀)) :=
    (hr.continuousAt (hU.mem_nhds hmem)).tendsto.comp hF
  have hleft : Tendsto (fun x => l (F x)) L (𝓝 (l F₀)) :=
    (hl.continuousAt (hU.mem_nhds hmem)).tendsto.comp hF
  have hnear : ∀ᶠ x in L, PerronData (F x) (lam (F x)) (r (F x)) (l (F x)) := by
    filter_upwards [hF.eventually (hU.mem_nhds hmem)] with x hx
    exact hdata _ hx
  let A : X → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := fun x => complexMatrixOperator (F x)
  let φ : X → (Fin n → ℂ) →L[ℂ] ℂ := fun x => complexFunctional (l (F x))
  let rc : X → Fin n → ℂ := fun x i => (r (F x) i:ℂ)
  let A₀ := complexMatrixOperator F₀
  let φ₀ := complexFunctional (l F₀)
  let rc₀ : Fin n → ℂ := fun i => (r F₀ i:ℂ)
  have hA : Tendsto A L (𝓝 A₀) := matrixOperator_continuous.continuousAt.tendsto.comp hF
  have hφ : Tendsto φ L (𝓝 φ₀) := functional_continuous.continuousAt.tendsto.comp hleft
  have hrc : Tendsto rc L (𝓝 rc₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hright) i)
  have hnorm : φ₀ rc₀=1 := by
    change complexFunctional (l F₀) rc₀=1
    rw [complexFunctional_apply]
    dsimp [rc₀]
    exact_mod_cast hbase.normalized
  have hsimple : ∀ x,(ContinuousLinearMap.id ℂ (Fin n → ℂ)-A₀) x=0 → ∃ c:ℂ,x=c • rc₀ := by
    intro x hx
    have hfix : A₀ x=x := (sub_eq_zero.mp hx).symm
    exact ⟨φ₀ x,hbase.simple x (by simpa [hlam₀] using hfix)⟩
  have hB : Tendsto (fun x => ContinuousLinearMap.id ℂ (Fin n → ℂ)-A x) L
      (𝓝 (ContinuousLinearMap.id ℂ (Fin n → ℂ)-A₀)) := tendsto_const_nhds.sub hA
  obtain ⟨C,hC,hcoerce⟩ := RestrictedInverseUniform.filter_complement_coercivity L
    (fun x => ContinuousLinearMap.id ℂ (Fin n → ℂ)-A x) φ
    (ContinuousLinearMap.id ℂ (Fin n → ℂ)-A₀) φ₀ rc₀ hB hφ
    (by rw [hnorm]; exact one_ne_zero) hsimple
  have hkernel : ∀ᶠ x in L, ∀ v,φ x v=0 → A x v=v → v=0 := by
    filter_upwards [hcoerce] with x hx
    intro v hv hfix
    have hb := hx v hv
    have hz : (ContinuousLinearMap.id ℂ (Fin n → ℂ)-A x) v=0 := sub_eq_zero.mpr hfix.symm
    rw [hz,norm_zero,mul_zero] at hb
    exact norm_le_zero_iff.mp hb
  have hlam2 : ∀ᶠ x in L, (2:ℂ)-(lam (F x):ℂ)≠0 := by
    filter_upwards [hlam.eventually_lt_const (show (1:ℝ)<3/2 by norm_num)] with x hx
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  have hex : ∀ᶠ x in L, ∃ K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
      IsRestrictedInverse (A x).toLinearMap K.toLinearMap (φ x).toLinearMap (rc x) := by
    filter_upwards [hnear,hkernel,hlam2] with x hx hk he
    apply RestrictedInverseUniform.restricted_inverse_exists_moving_eigenvalue
      (A x) (φ x) (rc x) (lam (F x):ℂ)
    · change complexFunctional (l (F x)) (rc x)=1
      rw [complexFunctional_apply]
      dsimp [rc]
      exact_mod_cast hx.normalized
    · funext i
      change (∑ j,(F x i j:ℂ)*(r (F x) j:ℂ))=(lam (F x):ℂ)*(r (F x) i:ℂ)
      exact_mod_cast hx.right_eigen i
    · exact functional_left_eigen _ _ _ hx.left_eigen
    · exact he
    · exact hk
  let K : X → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := fun x =>
    if h : ∃ K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ),
      IsRestrictedInverse (A x).toLinearMap K.toLinearMap (φ x).toLinearMap (rc x)
    then h.choose else 0
  have hK : ∀ᶠ x in L, IsRestrictedInverse (A x).toLinearMap (K x).toLinearMap
      (φ x).toLinearMap (rc x) := by
    filter_upwards [hex] with x hx
    simpa only [K,dif_pos hx] using hx.choose_spec
  have hreal : ∀ᶠ x in L, ∀ b : Fin n → ℝ, ∃ u : Fin n → ℝ,
      K x (fun i => (b i:ℂ))=fun i => (u i:ℂ) := by
    filter_upwards [hK,hkernel] with x hx hk
    exact restricted_inverse_real_of_complement (F x) (r (F x)) (l (F x)) (K x) hx hk
  have hKi : ∀ᶠ x in L, ∀ v, φ x (K x v)=0 ∧
      (ContinuousLinearMap.id ℂ (Fin n → ℂ)-A x) (K x v)=v-φ x v • rc x := by
    filter_upwards [hK] with x hx
    exact fun v => ⟨hx.kill_left v,hx.right_inverse v⟩
  obtain ⟨M,hM,hKM⟩ := RestrictedInverseUniform.filter_projected_inverse_bound L
    (fun x => ContinuousLinearMap.id ℂ (Fin n → ℂ)-A x) K φ rc
    (ContinuousLinearMap.id ℂ (Fin n → ℂ)-A₀) φ₀ rc₀ hB hφ hrc
    (by rw [hnorm]; exact one_ne_zero) hsimple hKi
  let b : ℝ := (Finset.univ.inf' Finset.univ_nonempty (l F₀))/2
  have hb : 0<b := by
    dsimp [b]
    exact half_pos ((Finset.lt_inf'_iff _).mpr (fun i _ => hbase.left_positive i))
  have hbi (i : Fin n) : b<l F₀ i := by
    have hh := Finset.inf'_le (l F₀) (Finset.mem_univ i)
    change (Finset.univ.inf' Finset.univ_nonempty (l F₀))/2<l F₀ i
    linarith [hbase.left_positive i]
  have hlow : ∀ᶠ x in L, ∀ i,b≤l (F x) i := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((tendsto_pi_nhds.mp hleft) i).eventually_const_le (hbi i)
  let Q : ℝ := ‖m₀‖+1
  let R : ℝ := ‖rc₀‖+1
  let P : ℝ := ‖φ₀‖+1
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hP : 0<P := by dsimp [P]; positivity
  have hqm : ∀ᶠ x in L, ‖m x‖≤Q := hm.norm.eventually_le_const (by dsimp [Q]; linarith)
  have hrm : ∀ᶠ x in L, ‖rc x‖≤R := hrc.norm.eventually_le_const (by dsimp [R]; linarith)
  have hlm : ∀ᶠ x in L, ‖φ x‖≤P := hφ.norm.eventually_le_const (by dsimp [P]; linarith)
  refine ⟨⟨fun x => lam (F x),fun x => r (F x),fun x => l (F x),K,
    r F₀,l F₀,by simpa only [hlam₀] using hbase,hlam,hright,hleft,hnear,hK,hreal,?_⟩⟩
  refine ⟨1+R+P+M+Q+M*Q,b,by positivity,hb,?_⟩
  filter_upwards [hKM,hlow,hqm,hrm,hlm] with x hk hlowx hqx hrx hlx
  have hq : ‖(fun i => (‖m x i‖:ℂ))‖≤Q := by
    apply pi_norm_le_iff_of_nonneg hQ.le |>.mpr
    intro i
    simpa using (norm_le_pi_norm (m x) i).trans hqx
  have hkq := (K x).le_opNorm (fun i => (‖m x i‖:ℂ))
  have hprod := mul_le_mul hk hq (norm_nonneg _) hM.le
  change ‖(fun i => (r (F x) i:ℂ))‖≤R at hrx
  change ‖complexFunctional (l (F x))‖≤P at hlx
  have hMQ : 0≤M*Q := mul_nonneg hM.le hQ.le
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by nlinarith [hkq.trans hprod],hlowx⟩

/-- At a regular point the canonical solution is continuous along the full
closed upper half-plane, including the real gap and support sides. -/
theorem regular_closed_upper_limit {n : ℕ}
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m) :
    Tendsto (Boundary.boundaryVector m) (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ))
      (𝓝 (Boundary.boundaryVector m (τ:ℂ))) := by
  have hregular : ∀ᶠ z : ℂ in 𝓝 (τ:ℂ), z.re ∉ Boundary.singularUnion m := by
    have hopen := (Boundary.family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
    exact (Complex.continuous_re.continuousAt (x := (τ:ℂ))).tendsto.eventually
      (hopen.mem_nhds (show (τ:ℂ).re ∈ (Boundary.singularUnion m)ᶜ from hτ))
  have hdom : Boundary.commonRegularDomain m ∈ 𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ) := by
    filter_upwards [self_mem_nhdsWithin,hregular.filter_mono nhdsWithin_le_nhds] with z hz hr
    by_cases hi : 0<z.im
    · exact Or.inl hi
    · have hi0 : z.im=0 := le_antisymm (le_of_not_gt hi) hz
      exact Or.inr ⟨z.re,hr,by apply Complex.ext <;> simp [hi0]⟩
  exact ((Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
    (τ:ℂ) (Or.inr ⟨τ,hτ,rfl⟩)).mono_of_mem_nhdsWithin hdom

/-- Complete moving Perron data for the actual boundary extension near a
regular edge or cusp, on the manuscript's closed upper half-plane domain. -/
theorem regular_frontier_varying_frame (external : ExternalContinuousPerron)
    {n : ℕ} (hn : 0<n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    Nonempty (VaryingFrame S (Boundary.boundaryVector m)
      (𝓝[ExternalAlgebraic.closedUpper] (τ:ℂ)) (Boundary.boundaryVector m (τ:ℂ))) := by
  apply varying_frame_exists external hn S hS hirr (Boundary.boundaryVector m) _ _
    (regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ)
    (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  intro lam r l hd
  exact regular_frontier_perron_one hn algebraic puiseux S a hS hirr m hupper heq
    τ i hfront hτ l lam hd.left_positive hd.left_eigen

end NonSymmetricDyson.Full.PerronContinuation
