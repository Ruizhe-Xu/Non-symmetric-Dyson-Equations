import Mathlib

/-! Actual bounded weighted-forest operators on complex ℓ².
The root/child decomposition is an arbitrary equivalence; no Dyson equation
or resolvent conclusion is an input to the construction. -/
noncomputable section
open scoped BigOperators ComplexConjugate ENNReal
set_option maxHeartbeats 800000
namespace NonSymmetricDyson.Paper.TreeOperators

universe u v
abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

variable {V : Type u} {Child : V → Type v} [∀ x, Fintype (Child x)]

def creationCoordinates (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (f : V → ℂ) (y : V) : ℂ :=
  match e.symm y with
  | Sum.inl _ => 0
  | Sum.inr a => (c a.1 a.2 : ℂ)*f a.1

@[simp] theorem creationCoordinates_root (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (f : V → ℂ) :
    creationCoordinates e c f (e (Sum.inl ()))=0 := by simp [creationCoordinates]

@[simp] theorem creationCoordinates_child (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (f : V → ℂ) (x : V) (j : Child x) :
    creationCoordinates e c f (e (Sum.inr ⟨x,j⟩))=(c x j : ℂ)*f x := by
  simp [creationCoordinates]

theorem summable_norm_sq (f : Hilbert V) : Summable (fun x => ‖f x‖^2) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

theorem tsum_norm_sq (f : Hilbert V) : ∑' x, ‖f x‖^2=‖f‖^2 := by
  simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f).symm

theorem creation_summable (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) (f : Hilbert V) :
    Summable (fun y => ‖creationCoordinates e c f y‖^2) := by
  classical
  have hrow (x : V) : (∑' j, ‖(c x j : ℂ)*f x‖^2) ≤ R*‖f x‖^2 := by
    simp only [tsum_fintype,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hc x) (sq_nonneg _)
  have hs : Summable (fun a : Σ x,Child x => ‖(c a.1 a.2 : ℂ)*f a.1‖^2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    exact ((summable_norm_sq f).mul_left R).of_nonneg_of_le
      (fun _ => tsum_nonneg (fun _ => sq_nonneg _)) hrow
  apply e.summable_iff.mp
  apply Summable.sum
  · simpa [creationCoordinates,Function.comp_def] using
      (summable_zero : Summable (fun _ : Unit => (0 : ℝ)))
  · simpa [creationCoordinates,Function.comp_def] using hs

theorem creation_tsum_bound (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) (f : Hilbert V) :
    ∑' y, ‖creationCoordinates e c f y‖^2 ≤ R*‖f‖^2 := by
  classical
  have hs := creation_summable e c R hR hc f
  have hsum : Summable (fun y : Unit ⊕ (Σ x,Child x) =>
      ‖creationCoordinates e c f (e y)‖^2) := e.summable_iff.mpr hs
  have hleft : Summable (fun y : Unit => ‖creationCoordinates e c f (e (Sum.inl y))‖^2) := by
    simpa [creationCoordinates] using (summable_zero : Summable (fun _ : Unit => (0 : ℝ)))
  have hright : Summable (fun y : Σ x,Child x =>
      ‖creationCoordinates e c f (e (Sum.inr y))‖^2) :=
    hsum.comp_injective (show Function.Injective (Sum.inr : (Σ x,Child x) → Unit ⊕ (Σ x,Child x)) from Sum.inr_injective)
  have hsσ : Summable (fun a : Σ x,Child x => ‖(c a.1 a.2 : ℂ)*f a.1‖^2) := by
    simpa [creationCoordinates] using hright
  rw [← e.tsum_eq (fun y => ‖creationCoordinates e c f y‖^2)]
  rw [Summable.tsum_sum (f := fun y : Unit ⊕ (Σ x,Child x) => ‖creationCoordinates e c f (e y)‖^2) hleft hright]
  simp only [creationCoordinates,Equiv.symm_apply_apply,norm_zero,zero_pow (by omega : 2≠0),
    tsum_zero,zero_add]
  rw [hsσ.tsum_sigma]
  calc
    _ ≤ ∑' x,R*‖f x‖^2 := by
      apply Summable.tsum_le_tsum
      · intro x
        simp only [tsum_fintype,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hc x) (sq_nonneg _)
      · exact (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mp hsσ |>.2
      · exact (summable_norm_sq f).mul_left R
    _ = R*‖f‖^2 := by rw [tsum_mul_left,tsum_norm_sq]

/-- The actual creation map preserves square summability. -/
def creationLinear (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) : Hilbert V →ₗ[ℂ] Hilbert V where
  toFun f := ⟨creationCoordinates e c f, memℓp_gen (by
    simpa using creation_summable e c R hR hc f)⟩
  map_add' f g := by
    ext y
    simp only [lp.coeFn_add]
    unfold creationCoordinates
    split <;> simp_all [mul_add]
  map_smul' a f := by
    ext y
    simp only [lp.coeFn_smul]
    unfold creationCoordinates
    split <;> simp_all [mul_assoc,mul_left_comm]

theorem creation_norm_bound (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) (f : Hilbert V) :
    ‖creationLinear e c R hR hc f‖ ≤ Real.sqrt R*‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  simpa [creationLinear,mul_pow,Real.sq_sqrt hR] using creation_tsum_bound e c R hR hc f

def creation (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) : Hilbert V →L[ℂ] Hilbert V :=
  (creationLinear e c R hR hc).mkContinuous (Real.sqrt R)
    (creation_norm_bound e c R hR hc)

@[simp] theorem creation_apply (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) (f : Hilbert V) (y : V) :
    creation e c R hR hc f y=creationCoordinates e c f y := rfl

theorem norm_creation (e : Unit ⊕ (Σ x,Child x) ≃ V)
    (c : ∀ x,Child x → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x, ∑ j,c x j^2 ≤ R) :
    ‖creation e c R hR hc‖ ≤ Real.sqrt R :=
  (creationLinear e c R hR hc).mkContinuous_norm_le (Real.sqrt_nonneg _)
    (creation_norm_bound e c R hR hc)

end NonSymmetricDyson.Paper.TreeOperators
