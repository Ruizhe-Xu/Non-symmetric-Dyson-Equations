import Dyson.Full.CyclicScalar
import Dyson.Full.EuclideanInverse

/-! Directed cycles of arbitrary positive length.  The inverse is computed by
an actual finite geometric sum.  No Fourier diagonalization is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set Fin.NatCast

namespace NonSymmetricDyson.Full.CyclicGeneral

variable (d : ℕ) [NeZero d]

/-- The convention is `(S u) i = u (i+1)`, with cyclic indices. -/
def cycle : Matrix (Fin d) (Fin d) ℝ := fun i j => if j = i+1 then 1 else 0

theorem cycle_nonnegative (i j : Fin d) : 0 ≤ cycle d i j := by
  unfold cycle
  split_ifs <;> norm_num

@[simp] theorem cycle_action (u : Fin d → ℂ) (i : Fin d) :
    Model.action (cycle d) u i = u (i+1) := by
  simp [Model.action_apply, cycle, apply_ite]

@[simp] theorem cycle_row_sum (i : Fin d) : ∑ j, cycle d i j = 1 := by
  simp [cycle]

theorem cycle_power (k : ℕ) (i j : Fin d) :
    (cycle d ^ k) i j = if j = i+(k : Fin d) then 1 else 0 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply, eq_comm]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [cycle, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [ih]
    simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]

theorem cycle_irreducible (i j : Fin d) : ∃ k : ℕ, 0 < k ∧ 0 < (cycle d ^ k) i j := by
  refine ⟨(j-i).val+d, ?_, ?_⟩
  · have hd := NeZero.pos d
    omega
  · rw [cycle_power]
    have he : i+(((j-i).val+d : ℕ) : Fin d) = j := by
      push_cast
      simp
    simp [he]

theorem cycle_not_symmetric (hd : 3 ≤ d) : ¬ Matrix.IsSymm (cycle d) := by
  intro hs
  have h := congrFun (congrFun hs (0 : Fin d)) (1 : Fin d)
  have h10 : (0 : Fin d) ≠ 1+1 := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_add, Fin.val_one'] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < d), Nat.mod_eq_of_lt (by omega : 1+1 < d)] at hv
    omega
  simpa [Matrix.transpose_apply, cycle, h10] using h

abbrev Space := EuclideanSpace ℂ (Fin d)

def shift : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
  LinearMap.toContinuousLinearMap (Model.action (cycle d))

def shift₂ : Space d →L[ℂ] Space d := EuclideanInverse.conjugate (shift d)

@[simp] theorem shift_apply (u : Fin d → ℂ) (i : Fin d) : shift d u i = u (i+1) :=
  cycle_action d u i

@[simp] theorem shift₂_apply (u : Space d) (i : Fin d) : shift₂ d u i = u (i+1) :=
  cycle_action d (WithLp.ofLp u) i

theorem shift_power (k : ℕ) (u : Fin d → ℂ) (i : Fin d) :
    (shift d ^ k) u i = u (i+(k : Fin d)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change shift d ((shift d ^ k) u) i = _
    rw [shift_apply, ih]
    simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]

theorem shift₂_power (k : ℕ) (u : Space d) (i : Fin d) :
    (shift₂ d ^ k) u i = u (i+(k : Fin d)) := by
  induction k generalizing i with
  | zero =>
    change u i = u (i+(0 : Fin d))
    rw [add_zero]
  | succ k ih =>
    rw [pow_succ']
    change shift₂ d ((shift₂ d ^ k) u) i = _
    rw [shift₂_apply, ih]
    congr 1
    change i+1+(k : Fin d) = i+((k+1 : ℕ) : Fin d)
    simp [Nat.cast_add, add_assoc, add_comm, add_left_comm]

theorem shift_period : shift d ^ d = 1 := by
  ext u i
  simp [shift_power]

theorem shift₂_period : shift₂ d ^ d = 1 := by
  ext u i
  rw [shift₂_power]
  change u (i+(d : Fin d)) = u i
  rw [Fin.natCast_self, add_zero]

theorem shift₂_isometry (u : Space d) : ‖shift₂ d u‖ = ‖u‖ := by
  have hs : ‖shift₂ d u‖^2 = ‖u‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, shift₂_apply]
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin d)) (fun i => ‖u i‖^2)
  nlinarith [norm_nonneg (shift₂ d u), norm_nonneg u]

theorem shift₂_norm_le : ‖shift₂ d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [shift₂_isometry, one_mul]

theorem pow_mod (ζ : ℂ) (hζ : ζ^d = 1) (n : ℕ) : ζ^(n%d) = ζ^n := by
  conv_rhs => rw [← Nat.mod_add_div n d, pow_add, pow_mul, hζ, one_pow, mul_one]

def eigenvector (ζ : ℂ) : Fin d → ℂ := fun i => ζ^i.val

theorem eigenvector_nonzero (ζ : ℂ) : eigenvector d ζ ≠ 0 := by
  intro he
  have := congrFun he (0 : Fin d)
  simpa [eigenvector] using this

theorem shift_eigenvector (ζ : ℂ) (hζ : ζ^d = 1) :
    shift d (eigenvector d ζ) = ζ • eigenvector d ζ := by
  ext i
  simp only [shift_apply, eigenvector, Pi.smul_apply, smul_eq_mul, Fin.val_add]
  rw [pow_mod d ζ hζ, pow_add, Fin.val_one', pow_mod d ζ hζ, pow_one]
  ring

theorem shift₂_eigenvector (ζ : ℂ) (hζ : ζ^d = 1) :
    shift₂ d (WithLp.toLp 2 (eigenvector d ζ)) =
      ζ • WithLp.toLp 2 (eigenvector d ζ) := by
  ext i
  exact congrFun (shift_eigenvector d ζ hζ) i

/-- Geometric numerator in the ordinary Euclidean space. -/
def numerator (q : ℂ) : Space d →L[ℂ] Space d :=
  ∑ k ∈ Finset.range d, (q • shift₂ d)^k

theorem numerator_identity (q : ℂ) :
    (1-q • shift₂ d) * numerator d q = (1-q^d) • (1 : Space d →L[ℂ] Space d) := by
  rw [numerator, mul_neg_geom_sum, smul_pow, shift₂_period]
  module

theorem numerator_identity_right (q : ℂ) :
    numerator d q * (1-q • shift₂ d) = (1-q^d) • (1 : Space d →L[ℂ] Space d) := by
  rw [numerator, geom_sum_mul_neg, smul_pow, shift₂_period]
  module

theorem numerator_continuous : Continuous (numerator d) := by
  unfold numerator
  fun_prop

theorem numerator_norm (q : ℂ) (hq : ‖q‖=1) (hqd : q^d=1) :
    ‖numerator d q‖ = d := by
  have hq0 : q ≠ 0 := by intro he; simp [he] at hq
  have hupper : ‖numerator d q‖ ≤ d := by
    calc
      _ ≤ ∑ k ∈ Finset.range d, ‖(q • shift₂ d)^k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range d, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (by
          rw [norm_smul, hq, one_mul]; exact shift₂_norm_le d))
      _ = d := by simp
  let v : Space d := WithLp.toLp 2 (eigenvector d q⁻¹)
  have hv : v ≠ 0 := by
    intro he
    apply eigenvector_nonzero d q⁻¹
    exact congrArg WithLp.ofLp he
  have hp : (q • shift₂ d) v = v := by
    rw [ContinuousLinearMap.smul_apply, shift₂_eigenvector d q⁻¹ (by simp [hqd]),
      smul_smul, mul_inv_cancel₀ hq0, one_smul]
  have hpk (k : ℕ) : ((q • shift₂ d)^k) v = v := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ']; change (q • shift₂ d) (((q • shift₂ d)^k) v) = v; rw [ih, hp]
  have hn : numerator d q v = (d : ℂ) • v := by
    simp [numerator, ContinuousLinearMap.sum_apply, hpk, Nat.cast_smul_eq_nsmul]
  have h := (numerator d q).le_opNorm v
  rw [hn, norm_smul] at h
  norm_num at h
  exact le_antisymm hupper (by nlinarith [norm_pos_iff.mpr hv])

end NonSymmetricDyson.Full.CyclicGeneral
