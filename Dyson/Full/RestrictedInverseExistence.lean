import Dyson.Full.RestrictedInverseUniform

noncomputable section
set_option maxRecDepth 4096
namespace NonSymmetricDyson.Full.RestrictedInverseUniform
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The actual restricted inverse of I−F for a moving Perron eigenvalue.
The full operator may be singular; only its complementary kernel is required
to vanish. Unlike a normalized-Perron construction, λ need not equal one. -/
theorem restricted_inverse_exists_moving_eigenvalue
    (F : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) (r : E) (lam : ℂ)
    (hnorm : φ r = 1) (hFr : F r = lam • r)
    (hleft : ∀ x, φ (F x) = lam * φ x) (hlam : 2-lam ≠ 0)
    (hkernel : ∀ x, φ x = 0 → F x = x → x = 0) :
    ∃ K : E →L[ℂ] E, Singularities.IsRestrictedInverse F.toLinearMap K.toLinearMap
      φ.toLinearMap r := by
  let P : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - φ.smulRight r
  let L : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - F + φ.smulRight r
  have hPx (x : E) : P x = x-φ x • r := rfl
  have hLx (x : E) : L x = x-F x+φ x • r := rfl
  have hφL (x : E) : φ (L x) = (2-lam)*φ x := by
    rw [hLx, map_add, map_sub, map_smul, hleft, hnorm]
    simp only [smul_eq_mul]
    ring
  have hφP (x : E) : φ (P x) = 0 := by simp [hPx,hnorm]
  have hinj : Function.Injective L.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change L x = 0 at hx
    have hφx : φ x = 0 := by
      have hh : (2-lam)*φ x=0 := by rw [← hφL,hx,map_zero]
      exact (mul_eq_zero.mp hh).resolve_left hlam
    have hfix : F x=x := by
      have hh := hx
      rw [hLx,hφx,zero_smul,add_zero] at hh
      exact (sub_eq_zero.mp hh).symm
    exact hkernel x hφx hfix
  let e : E ≃L[ℂ] E := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  let K : E →L[ℂ] E := e.symm.toContinuousLinearMap.comp P
  have hLK (x : E) : L (K x)=P x := e.apply_symm_apply (P x)
  have hφK (x : E) : φ (K x)=0 := by
    have hh : (2-lam)*φ (K x)=0 := by rw [← hφL,hLK,hφP]
    exact (mul_eq_zero.mp hh).resolve_left hlam
  refine ⟨K,?_,hφK,?_,?_⟩
  · change K r=0
    have hp : P r=0 := by simp [hPx,hnorm]
    simp [K,hp]
  · intro x
    apply hinj
    change L (K (x-F x)) = L (x-φ x • r)
    rw [hLK,hPx,hLx]
    simp only [map_sub,map_smul,hleft,hFr,hnorm,smul_eq_mul,
      smul_smul,sub_smul]
    module
  · intro x
    have hh := hLK x
    rw [hLx,hφK,zero_smul,add_zero,hPx] at hh
    exact hh

end NonSymmetricDyson.Full.RestrictedInverseUniform
