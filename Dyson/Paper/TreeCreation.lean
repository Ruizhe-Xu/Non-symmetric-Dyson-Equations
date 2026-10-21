import Dyson.Paper.TreeHilbert

/-! Adjoint coordinates and the bounded self-adjoint Jacobi operator for an
arbitrary weighted forest. Every operator here acts on the actual ℓ² space. -/
noncomputable section
open scoped BigOperators ENNReal ComplexConjugate Classical InnerProduct
namespace NonSymmetricDyson.Paper.TreeOperators
universe u v
variable {V : Type u} {Child : V → Type v} [∀ x,Fintype (Child x)]
variable (e : Unit ⊕ (Σ x,Child x) ≃ V) (c : ∀ x,Child x → ℝ)
variable (R : ℝ) (hR : 0 ≤ R) (hc : ∀ x,∑ j,c x j^2 ≤ R)

theorem creation_delta (x : V) :
    creation e c R hR hc (delta x) = ∑ j : Child x,(c x j : ℂ) • delta (e (Sum.inr ⟨x,j⟩)) := by
  classical
  ext y
  obtain ⟨a,rfl⟩ := e.surjective y
  cases a with
  | inl a =>
    simp [creation_apply,creationCoordinates,delta_apply,lp.coeFn_sum,lp.coeFn_smul,e.injective.eq_iff]
  | inr a =>
    obtain ⟨v,j⟩ := a
    by_cases hv : v=x
    · subst v
      simp [creation_apply,creationCoordinates,delta_apply,lp.coeFn_sum,lp.coeFn_smul,e.injective.eq_iff]
    · have hh (k : Child x) : e (Sum.inr ⟨v,j⟩) ≠ e (Sum.inr ⟨x,k⟩) := by
        intro h
        have hs := congrArg Sigma.fst (Sum.inr.inj (e.injective h))
        exact hv hs
      simp [creation_apply,creationCoordinates,delta_apply,lp.coeFn_sum,lp.coeFn_smul,hv,hh]

theorem creation_adjoint_apply (f : Hilbert V) (x : V) :
    (creation e c R hR hc).adjoint f x =
      ∑ j : Child x,(c x j : ℂ)*f (e (Sum.inr ⟨x,j⟩)) := by
  rw [← inner_delta_left x ((creation e c R hR hc).adjoint f),
    ContinuousLinearMap.adjoint_inner_right,creation_delta]
  simp only [sum_inner,inner_smul_left,inner_delta_left,Complex.conj_ofReal]

/-- The tree Jacobi operator on the actual Hilbert space. -/
def jacobi (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x,|a x| ≤ A) :
    Hilbert V →L[ℂ] Hilbert V :=
  diagonal a A hA ha + creation e c R hR hc + (creation e c R hR hc).adjoint

theorem jacobi_selfAdjoint (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) : IsSelfAdjoint (jacobi e c R hR hc a A hA ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [jacobi,map_add,ContinuousLinearMap.adjoint_adjoint,
    (diagonal_selfAdjoint a A hA ha).adjoint_eq]
  abel

theorem norm_jacobi (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) :
    ‖jacobi e c R hR hc a A hA ha‖ ≤ A+2*Real.sqrt R := by
  calc
    _ ≤ (‖diagonal a A hA ha‖+‖creation e c R hR hc‖)+‖(creation e c R hR hc).adjoint‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ = ‖diagonal a A hA ha‖+2*‖creation e c R hR hc‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      ring
    _ ≤ A+2*Real.sqrt R := by
      gcongr
      · exact norm_diagonal a A hA ha
      · exact norm_creation e c R hR hc

@[simp] theorem jacobi_apply (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) (f : Hilbert V) (x : V) :
    jacobi e c R hR hc a A hA ha f x =
      (a x : ℂ)*f x+creationCoordinates e c f x+
        ∑ j : Child x,(c x j : ℂ)*f (e (Sum.inr ⟨x,j⟩)) := by
  simp [jacobi,creation_adjoint_apply]

end NonSymmetricDyson.Paper.TreeOperators
