import Dyson.Paper.SingularitiesNormalization
import Dyson.Full.PerronVarying

/-! The manuscript's unique Euclidean-right normalization imposed on the
whole continuous Perron frame. The stable projection and K are unchanged. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Perron
open Full Full.Singularities Full.PerronContinuation
variable {X : Type*} {n : ℕ}

def rightLength (r : Fin n → ℝ) : ℝ := Real.sqrt (∑ i,r i^2)

theorem rightLength_pos (hn : 0<n) (r : Fin n → ℝ) (hr : ∀ i,0<r i) : 0<rightLength r := by
  apply Real.sqrt_pos.mpr
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) ⟨⟨0,hn⟩,Finset.mem_univ _⟩

theorem rightLength_tendsto {L : Filter X} (r : X → Fin n → ℝ) (r₀ : Fin n → ℝ)
    (hr : Tendsto r L (𝓝 r₀)) : Tendsto (fun x => rightLength (r x)) L (𝓝 (rightLength r₀)) := by
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  exact tendsto_finset_sum _ (fun i _ => ((tendsto_pi_nhds.mp hr) i).pow 2)

theorem rescaled_functional [Nonempty (Fin n)] (t : ℝ) (l : Fin n → ℝ) :
    complexFunctional (fun i => t*l i)=(t:ℂ) • complexFunctional l := by
  ext x
  simp only [complexFunctional_apply,Complex.ofReal_mul,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rescaled_right (t : ℝ) (r : Fin n → ℝ) :
    (fun i => ((r i/t:ℝ):ℂ))=(t:ℂ)⁻¹ • (fun i => (r i:ℂ)) := by
  ext i
  simp [div_eq_mul_inv,mul_comm]

theorem rescaled_restricted_inverse [Nonempty (Fin n)] (F : Matrix (Fin n) (Fin n) ℝ)
    (K : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (r l : Fin n → ℝ) (t : ℝ) (ht : t≠0)
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K.toLinearMap
      (complexFunctional l).toLinearMap (fun i => (r i:ℂ))) :
    IsRestrictedInverse (complexMatrixOperator F).toLinearMap K.toLinearMap
      (complexFunctional (fun i => t*l i)).toLinearMap (fun i => ((r i/t:ℝ):ℂ)) := by
  have htc : (t:ℂ)≠0 := by exact_mod_cast ht
  have hp (x : Fin n → ℂ) :
      complexFunctional (fun i => t*l i) x • (fun i => ((r i/t:ℝ):ℂ))=
        complexFunctional l x • (fun i => (r i:ℂ)) := by
    rw [rescaled_functional,rescaled_right,ContinuousLinearMap.smul_apply,smul_smul,smul_eq_mul]
    congr 1
    field_simp
  refine ⟨?_,?_,?_,?_⟩
  · rw [rescaled_right,map_smul,hK.kill_right,smul_zero]
  · intro x
    change complexFunctional (fun i => t*l i) (K x)=0
    have hz : complexFunctional l (K x)=0 := hK.kill_left x
    rw [rescaled_functional,ContinuousLinearMap.smul_apply,hz,smul_zero]
  · intro x
    change K (x-complexMatrixOperator F x)=x-complexFunctional (fun i => t*l i) x • (fun i => ((r i/t:ℝ):ℂ))
    rw [hp]
    exact hK.left_inverse x
  · intro x
    change K x-complexMatrixOperator F (K x)=x-complexFunctional (fun i => t*l i) x • (fun i => ((r i/t:ℝ):ℂ))
    rw [hp]
    exact hK.right_inverse x

/-- Every genuine varying frame admits the exact right-unit normalization
required in the revised manuscript, with the same λ and restricted inverse. -/
theorem normalized_varying_frame (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ) (m : X → Fin n → ℂ) (L : Filter X) (m₀ : Fin n → ℂ)
    (d : VaryingFrame S m L m₀) :
    ∃ e : VaryingFrame S m L m₀,
      e.lam=d.lam ∧ e.K=d.K ∧
      (∀ x i,e.r x i=d.r x i/rightLength (d.r x)) ∧
      (∀ x i,e.l x i=rightLength (d.r x)*d.l x i) ∧
      (∑ i,e.r₀ i^2=1) ∧ ∀ᶠ x in L,∑ i,e.r x i^2=1 := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let t : X → ℝ := fun x => rightLength (d.r x)
  let t₀ := rightLength d.r₀
  have ht₀ : 0<t₀ := rightLength_pos hn d.r₀ d.center.right_positive
  have htlim : Tendsto t L (𝓝 t₀) := rightLength_tendsto d.r d.r₀ d.right_limit
  have hrLim : Tendsto (fun x i => d.r x i/t x) L (𝓝 (fun i => d.r₀ i/t₀)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((tendsto_pi_nhds.mp d.right_limit) i).div htlim ht₀.ne'
  have hlLim : Tendsto (fun x i => t x*d.l x i) L (𝓝 (fun i => t₀*d.l₀ i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact htlim.mul ((tendsto_pi_nhds.mp d.left_limit) i)
  have hcenter := SingularitiesNormalization.normalized_perron_data_explicit hn _ _ _ _ d.center
  have hnear : ∀ᶠ x in L,PerronData (saturatedMatrix S (m x)) (d.lam x)
      (fun i => d.r x i/t x) (fun i => t x*d.l x i) := by
    filter_upwards [d.nearby] with x hx
    exact (SingularitiesNormalization.normalized_perron_data_explicit hn _ _ _ _ hx).1
  have hrestricted : ∀ᶠ x in L,IsRestrictedInverse
      (complexMatrixOperator (saturatedMatrix S (m x))).toLinearMap (d.K x).toLinearMap
      (complexFunctional (fun i => t x*d.l x i)).toLinearMap (fun i => ((d.r x i/t x:ℝ):ℂ)) := by
    filter_upwards [d.nearby,d.restricted] with x hx hK
    exact rescaled_restricted_inverse _ _ _ _ _ (rightLength_pos hn _ hx.right_positive).ne' hK
  obtain ⟨B,b,hB,hb,hbounds⟩ := d.uniform
  let B' := 1+B+(2/t₀)*B+(t₀+1)*B
  have hB' : 0<B' := by dsimp [B']; positivity
  have hsmall : ∀ᶠ x in L,t₀/2≤t x ∧ t x≤t₀+1 :=
    (htlim.eventually_const_le (by linarith)).and (htlim.eventually_le_const (by linarith))
  have hnewbounds : ∀ᶠ x in L,
      ‖(fun i => ((d.r x i/t x:ℝ):ℂ))‖≤B' ∧
      ‖complexFunctional (fun i => t x*d.l x i)‖≤B' ∧ ‖d.K x‖≤B' ∧
      ‖(fun i => (‖m x i‖:ℂ))‖≤B' ∧ ‖d.K x (fun i => (‖m x i‖:ℂ))‖≤B' ∧
      ∀ i,(t₀/2)*b≤t x*d.l x i := by
    filter_upwards [hbounds,hsmall] with x hx ht
    have htx : 0<t x := (half_pos ht₀).trans_le ht.1
    have hterm1 : 0≤(2/t₀)*B := by positivity
    have hterm2 : 0≤(t₀+1)*B := by positivity
    have hBB : B≤B' := by dsimp [B']; linarith
    have hrB : ‖(fun i => ((d.r x i/t x:ℝ):ℂ))‖≤(2/t₀)*B := by
      rw [rescaled_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htx]
      apply mul_le_mul _ hx.1 (norm_nonneg _) (by positivity)
      have hi := inv_anti₀ (half_pos ht₀) ht.1
      simpa [div_eq_mul_inv] using hi
    have hlB : ‖complexFunctional (fun i => t x*d.l x i)‖≤(t₀+1)*B := by
      rw [rescaled_functional,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htx]
      exact mul_le_mul ht.2 hx.2.1 (norm_nonneg _) (by positivity)
    exact ⟨hrB.trans (by dsimp [B']; linarith),hlB.trans (by dsimp [B']; linarith),
      hx.2.2.1.trans hBB,hx.2.2.2.1.trans hBB,hx.2.2.2.2.1.trans hBB,
      fun i => mul_le_mul ht.1 (hx.2.2.2.2.2 i) hb.le htx.le⟩
  let e : VaryingFrame S m L m₀ := {
    lam := d.lam, r := fun x i => d.r x i/t x, l := fun x i => t x*d.l x i, K := d.K,
    r₀ := fun i => d.r₀ i/t₀,l₀ := fun i => t₀*d.l₀ i,
    center := hcenter.1,lam_limit := d.lam_limit,right_limit := hrLim,left_limit := hlLim,
    nearby := hnear,restricted := hrestricted,real_preserving := d.real_preserving,
    uniform := ⟨B',(t₀/2)*b,hB',mul_pos (half_pos ht₀) hb,hnewbounds⟩ }
  refine ⟨e,rfl,rfl,fun _ _ => rfl,fun _ _ => rfl,hcenter.2.1,?_⟩
  filter_upwards [d.nearby] with x hx
  exact (SingularitiesNormalization.normalized_perron_data_explicit hn _ _ _ _ hx).2.1

end NonSymmetricDyson.Paper.Perron
