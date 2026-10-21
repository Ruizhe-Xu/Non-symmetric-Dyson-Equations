import Dyson.Full.PerronExistence

/-! Realness and actual quadratic coefficients of the complex restricted
inverse. Every step is finite-dimensional linear algebra; no reality or
coefficient identity is assumed. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The complex restricted inverse of a real matrix maps real inputs to real
outputs. Its imaginary part is a fixed vector annihilated by the normalized
left functional, hence vanishes by the simple eigenspace identity. -/
theorem restricted_inverse_real_input
    (F : ι → ι → ℝ) (r l : ι → ℝ)
    (K : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hK : IsRestrictedInverse (complexMatrixOperator F).toLinearMap K
      (complexFunctional l).toLinearMap (fun i => (r i : ℂ)))
    (hsimple : ∀ x : ι → ℂ, complexMatrixOperator F x = x →
      x = complexFunctional l x • (fun i => (r i : ℂ)))
    (b : ι → ℝ) :
    ∃ u : ι → ℝ, K (fun i => (b i : ℂ)) = (fun i => (u i : ℂ)) ∧
      (∑ i, l i * u i = 0) ∧
      ∀ i, u i - ∑ j, F i j * u j = b i - r i * (∑ j, l j * b j) := by
  let x : ι → ℂ := K (fun i => (b i : ℂ))
  let v : ι → ℝ := fun i => (x i).im
  have hright : x - complexMatrixOperator F x =
      (fun i => (b i : ℂ)) - complexFunctional l (fun i => (b i : ℂ)) •
        (fun i => (r i : ℂ)) := hK.right_inverse _
  have hleft : complexFunctional l x = 0 := hK.kill_left _
  have hvi (i : ι) : v i - ∑ j, F i j * v j = 0 := by
    have h := congrArg Complex.im (congrFun hright i)
    simpa [complexMatrixOperator_apply, complexFunctional, Complex.mul_im, v] using h
  have hvleft : ∑ i, l i * v i = 0 := by
    have h := congrArg Complex.im hleft
    simpa [complexFunctional, Complex.mul_im, v] using h
  have hvfixed : complexMatrixOperator F (fun i => (v i : ℂ)) =
      (fun i => (v i : ℂ)) := by
    funext i
    change (∑ j, (F i j : ℂ) * (v j : ℂ)) = (v i : ℂ)
    exact_mod_cast (sub_eq_zero.mp (hvi i)).symm
  have hvfunctional : complexFunctional l (fun i => (v i : ℂ)) = 0 := by
    rw [complexFunctional_apply]
    exact_mod_cast hvleft
  have hvzero : (fun i => (v i : ℂ)) = 0 := by
    rw [hsimple _ hvfixed, hvfunctional, zero_smul]
  have hv (i : ι) : v i = 0 := by
    have h := congrArg Complex.re (congrFun hvzero i)
    simpa using h
  let u : ι → ℝ := fun i => (x i).re
  have hreal : x = (fun i => (u i : ℂ)) := by
    funext i
    apply Complex.ext
    · rfl
    · exact hv i
  refine ⟨u, hreal, ?_, ?_⟩
  · have h := congrArg Complex.re hleft
    simpa [complexFunctional, Complex.mul_re, u] using h
  · intro i
    have h := congrArg Complex.re (congrFun hright i)
    simpa [complexMatrixOperator_apply, complexFunctional, Complex.mul_re, u,
      mul_comm] using h

/-- A genuine complex stable inverse and a real quadratic coefficient vector
are constructed from normalized positive Perron data. -/
theorem quadratic_stable_data_exists
    (F : ι → ι → ℝ) (p r l : ι → ℝ)
    (hnorm : ∑ i, l i * r i = 1)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j)
    (hsimple : ∀ x : ι → ℂ, complexMatrixOperator F x = x →
      x = complexFunctional l x • (fun i => (r i : ℂ))) :
    ∃ (K : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (u : ι → ℝ),
      IsRestrictedInverse (complexMatrixOperator F).toLinearMap K
        (complexFunctional l).toLinearMap (fun i => (r i : ℂ)) ∧
      K (fun i => (p i : ℂ) * (r i : ℂ)^2) = (fun i => (u i : ℂ)) ∧
      (∑ i, l i * u i = 0) ∧
      (∀ i, u i - ∑ j, F i j * u j =
        p i * r i^2 - r i * quadraticCoefficient p l r) ∧
      complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ)^2) =
        (quadraticCoefficient p l r : ℂ) ∧
      complexFunctional l (fun i => (p i : ℂ) * (r i : ℂ) *
        (complexMatrixOperator F (K (fun j => (p j : ℂ) * (r j : ℂ)^2)) i +
          K (fun j => (p j : ℂ) * (r j : ℂ)^2) i)) =
        (cubicCoefficient F p l r u : ℂ) := by
  have hnormC : complexFunctional l (fun i => (r i : ℂ)) = 1 := by
    rw [complexFunctional_apply]
    exact_mod_cast hnorm
  have hFrC : complexMatrixOperator F (fun i => (r i : ℂ)) =
      (fun i => (r i : ℂ)) := by
    funext i
    change (∑ j, (F i j : ℂ) * (r j : ℂ)) = (r i : ℂ)
    exact_mod_cast hFr i
  obtain ⟨K, hK⟩ := restricted_inverse_exists (complexMatrixOperator F).toLinearMap
    (complexFunctional l).toLinearMap (fun i => (r i : ℂ)) hnormC hFrC
    (complexFunctional_left_eigenvector F l hlF) hsimple
  obtain ⟨u, huK, hul, hu⟩ := restricted_inverse_real_input F r l K hK hsimple
    (fun i => p i * r i^2)
  have huK' : K (fun i => (p i : ℂ) * (r i : ℂ)^2) = (fun i => (u i : ℂ)) := by
    simpa using huK
  refine ⟨K, u, hK, huK', hul, ?_, ?_, ?_⟩
  · simpa [quadraticCoefficient, mul_assoc] using hu
  · simp [complexFunctional, quadraticCoefficient, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]
  · rw [huK']
    simp [complexFunctional, complexMatrixOperator_apply, cubicCoefficient,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, mul_add, add_comm,
      mul_left_comm, mul_comm, mul_assoc]

end NonSymmetricDyson.Full.Singularities
