import Dyson.Paper.TreeOperators

/-! Coordinate restriction, coordinate functionals, root unit vectors, and
real diagonal operators on the concrete complex ℓ² spaces. -/
noncomputable section
open scoped BigOperators ENNReal ComplexConjugate Classical
namespace NonSymmetricDyson.Paper.TreeOperators
universe u w
variable {V : Type u} {W : Type w}

def restrictLinear (e : W ↪ V) : Hilbert V →ₗ[ℂ] Hilbert W where
  toFun f := ⟨fun y => f (e y),memℓp_gen (by
    simpa using (summable_norm_sq f).comp_injective e.injective)⟩
  map_add' f g := by ext y; rfl
  map_smul' a f := by ext y; rfl

theorem restrict_norm_bound (e : W ↪ V) (f : Hilbert V) :
    ‖restrictLinear e f‖ ≤ ‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg _)
  have hs := (summable_norm_sq f).comp_injective e.injective
  have hh := Summable.tsum_le_tsum_of_inj
    (f := fun y : W => ‖f (e y)‖^2) (g := fun x : V => ‖f x‖^2) e e.injective
    (fun _ _ => sq_nonneg _) (fun _ => le_rfl) hs (summable_norm_sq f)
  rw [tsum_norm_sq f] at hh
  simpa using hh

def restrict (e : W ↪ V) : Hilbert V →L[ℂ] Hilbert W :=
  (restrictLinear e).mkContinuous 1 (fun f => by simpa using restrict_norm_bound e f)

@[simp] theorem restrict_apply (e : W ↪ V) (f : Hilbert V) (y : W) :
    restrict e f y=f (e y) := rfl

theorem norm_restrict (e : W ↪ V) : ‖restrict e‖ ≤ 1 :=
  (restrictLinear e).mkContinuous_norm_le zero_le_one
    (fun f => by simpa using restrict_norm_bound e f)

def evalLinear (x : V) : Hilbert V →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def eval (x : V) : Hilbert V →L[ℂ] ℂ :=
  (evalLinear x).mkContinuous 1 (fun f => by
    simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f x)

@[simp] theorem eval_apply (x : V) (f : Hilbert V) : eval x f=f x := rfl

def delta (x : V) : Hilbert V := lp.single 2 x 1

@[simp] theorem delta_apply (x y : V) : delta x y=if y=x then 1 else 0 := by
  classical
  simp [delta,lp.coeFn_single,Pi.single_apply]

@[simp] theorem norm_delta (x : V) : ‖delta x‖=1 := by
  classical
  simp [delta,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]

@[simp] theorem inner_delta_left (x : V) (f : Hilbert V) :
    inner ℂ (delta x) f=f x := by
  classical
  simp [delta,lp.inner_single_left]

/-- A bounded real potential gives an actual bounded diagonal map. -/
def diagonalLinear (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x,|a x| ≤ A) :
    Hilbert V →ₗ[ℂ] Hilbert V where
  toFun f := ⟨fun x => (a x : ℂ)*f x,memℓp_gen (by
    have hsum := (summable_norm_sq f).mul_left (A^2)
    have hs : Summable (fun x => ‖(a x : ℂ)*f x‖^2) :=
      hsum.of_nonneg_of_le (fun _ => sq_nonneg _) (fun x => by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
        gcongr
        exact ha x)
    simpa using hs)⟩
  map_add' _ _ := by ext x; simp [mul_add]
  map_smul' _ _ := by ext x; simp [mul_assoc,mul_left_comm]

theorem diagonal_norm_bound (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) (f : Hilbert V) :
    ‖diagonalLinear a A hA ha f‖ ≤ A*‖f‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  have hs : Summable (fun x => ‖(a x : ℂ)*f x‖^2) :=
    summable_norm_sq (diagonalLinear a A hA ha f)
  have hb : ∑' x, ‖(a x : ℂ)*f x‖^2 ≤ ∑' x,A^2*‖f x‖^2 := by
    apply Summable.tsum_le_tsum _ hs ((summable_norm_sq f).mul_left (A^2))
    intro x
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow]
    gcongr
    exact ha x
  simpa [diagonalLinear,mul_pow,tsum_mul_left,tsum_norm_sq] using hb

def diagonal (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ x,|a x| ≤ A) :
    Hilbert V →L[ℂ] Hilbert V :=
  (diagonalLinear a A hA ha).mkContinuous A (diagonal_norm_bound a A hA ha)

@[simp] theorem diagonal_apply (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) (f : Hilbert V) (x : V) :
    diagonal a A hA ha f x=(a x : ℂ)*f x := rfl

theorem norm_diagonal (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) : ‖diagonal a A hA ha‖ ≤ A :=
  (diagonalLinear a A hA ha).mkContinuous_norm_le hA (diagonal_norm_bound a A hA ha)

theorem diagonal_selfAdjoint (a : V → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ x,|a x| ≤ A) : IsSelfAdjoint (diagonal a A hA ha) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  simp only [lp.inner_eq_tsum,diagonal_apply]
  apply tsum_congr
  intro x
  simp [RCLike.inner_apply,mul_assoc,mul_comm,mul_left_comm]

end NonSymmetricDyson.Paper.TreeOperators
