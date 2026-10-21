import Mathlib
import Dyson.Model
import Dyson.Full.Singularities

/-! The original Markov proof's weighted Jensen and Doeblin argument.
All matrices, weighted norms and remainders here are actual finite objects.
No spectral-gap or contraction conclusion is supplied as an external theorem. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Paper.Perron

variable {ι : Type*} [Fintype ι]

def weightedSquare (π : ι → ℝ) (f : ι → ℂ) : ℝ := ∑ i, π i * ‖f i‖^2

def weightedEmbedding (π : ι → ℝ) : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun f := WithLp.toLp 2 (fun i => (Real.sqrt (π i) : ℂ) * f i)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp; ring

def weightedNorm (π : ι → ℝ) (f : ι → ℂ) : ℝ := ‖weightedEmbedding π f‖

theorem weightedNorm_nonneg (π : ι → ℝ) (f : ι → ℂ) : 0 ≤ weightedNorm π f :=
  norm_nonneg _

@[simp] theorem weightedNorm_zero (π : ι → ℝ) : weightedNorm π 0 = 0 := by
  simp [weightedNorm]

theorem weightedNorm_add_le (π : ι → ℝ) (f g : ι → ℂ) :
    weightedNorm π (f+g) ≤ weightedNorm π f + weightedNorm π g := by
  simpa [weightedNorm] using norm_add_le (weightedEmbedding π f) (weightedEmbedding π g)

theorem weightedNorm_sub_le (π : ι → ℝ) (f g : ι → ℂ) :
    weightedNorm π f - weightedNorm π g ≤ weightedNorm π (f-g) := by
  simpa [weightedNorm] using norm_sub_norm_le (weightedEmbedding π f) (weightedEmbedding π g)

theorem weightedNorm_smul (π : ι → ℝ) (c : ℂ) (f : ι → ℂ) :
    weightedNorm π (c • f) = ‖c‖ * weightedNorm π f := by
  simp [weightedNorm, norm_smul]

theorem weightedNorm_sum_le {κ : Type*} (π : ι → ℝ) (s : Finset κ)
    (f : κ → ι → ℂ) : weightedNorm π (∑ k ∈ s, f k) ≤ ∑ k ∈ s, weightedNorm π (f k) := by
  simpa [weightedNorm] using norm_sum_le s (fun k => weightedEmbedding π (f k))

theorem weightedNorm_sq (π : ι → ℝ) (hπ : ∀ i, 0 ≤ π i) (f : ι → ℂ) :
    weightedNorm π f ^ 2 = weightedSquare π f := by
  rw [weightedNorm, EuclideanSpace.norm_sq_eq]
  unfold weightedSquare
  apply Finset.sum_congr rfl
  intro i _
  change ‖(Real.sqrt (π i) : ℂ) * f i‖^2 = π i * ‖f i‖^2
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [Real.sq_sqrt (hπ i)]

private theorem complex_norm_sq_parts (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem weightedSquare_parts (π : ι → ℝ) (f : ι → ℂ) :
    weightedSquare π f = (∑ i, π i * (f i).re^2) + ∑ i, π i * (f i).im^2 := by
  simp only [weightedSquare, complex_norm_sq_parts, mul_add, Finset.sum_add_distrib]

/-- Jensen's inequality in the stationary weighted L² norm, proved by the
nonnegative real and imaginary variance identities. -/
theorem markov_weightedSquare_contraction (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hπ : ∀ i, 0 ≤ π i)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i * Q i j = π j) (f : ι → ℂ) :
    weightedSquare π (Model.action Q f) ≤ weightedSquare π f := by
  have hre : ∀ i, ∑ j, Q i j * (f j).re = (Model.action Q f i).re := by
    intro i
    simp [Model.action_apply, Complex.re_sum]
  have him : ∀ i, ∑ j, Q i j * (f j).im = (Model.action Q f i).im := by
    intro i
    simp [Model.action_apply, Complex.im_sum]
  have hr := Full.Singularities.stationary_variance_identity Q π
    (fun i => (f i).re) (fun i => (Model.action Q f i).re) hrow hstat hre
  have hi := Full.Singularities.stationary_variance_identity Q π
    (fun i => (f i).im) (fun i => (Model.action Q f i).im) hrow hstat him
  have hr0 : 0 ≤ ∑ i, ∑ j, π i * Q i j * ((f j).re - (Model.action Q f i).re)^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hπ i) (hQ i j)) (sq_nonneg _)))
  have hi0 : 0 ≤ ∑ i, ∑ j, π i * Q i j * ((f j).im - (Model.action Q f i).im)^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hπ i) (hQ i j)) (sq_nonneg _)))
  rw [weightedSquare_parts, weightedSquare_parts]
  linarith

theorem markov_weightedNorm_contraction (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hπ : ∀ i, 0 ≤ π i)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i * Q i j = π j) (f : ι → ℂ) :
    weightedNorm π (Model.action Q f) ≤ weightedNorm π f := by
  have hh := markov_weightedSquare_contraction Q π hQ hπ hrow hstat f
  rw [← weightedNorm_sq π hπ, ← weightedNorm_sq π hπ] at hh
  nlinarith [weightedNorm_nonneg π f, weightedNorm_nonneg π (Model.action Q f)]

/-- The actual Doeblin remainder matrix in the source. -/
def doeblinRemainder (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j - θ*π j)/(1-θ)

theorem doeblin_nonnegative (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1) (hminor : ∀ i j, θ*π j ≤ A i j) :
    ∀ i j, 0 ≤ doeblinRemainder A π θ i j :=
  fun i j => div_nonneg (sub_nonneg.mpr (hminor i j)) (by linarith)

theorem doeblin_stochastic (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1) (hrow : ∀ i, ∑ j, A i j = 1) (hπ : ∑ j, π j = 1) :
    ∀ i, ∑ j, doeblinRemainder A π θ i j = 1 := by
  intro i
  simp only [doeblinRemainder, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hrow i, hπ, mul_one]
  exact div_self (by linarith)

theorem doeblin_stationary (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1) (hstat : ∀ j, ∑ i, π i*A i j = π j) (hπ : ∑ j, π j = 1) :
    ∀ j, ∑ i, π i * doeblinRemainder A π θ i j = π j := by
  intro j
  simp only [doeblinRemainder, ← mul_div_assoc, ← Finset.sum_div, mul_sub,
    Finset.sum_sub_distrib]
  have he : (∑ i, π i*(θ*π j)) = θ*π j := by rw [← Finset.sum_mul, hπ, one_mul]
  rw [hstat j, he]
  field_simp [show 1-θ ≠ 0 by linarith]

theorem doeblin_entry_decomposition (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1) (i j : ι) :
    A i j = θ*π j + (1-θ)*doeblinRemainder A π θ i j := by
  unfold doeblinRemainder
  rw [mul_div_cancel₀ _ (by linarith : 1-θ ≠ 0)]
  ring

theorem doeblin_zero_mean_identity (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1) (f : ι → ℂ) (hmean : ∑ i, (π i : ℂ)*f i = 0) :
    Model.action A f = ((1-θ : ℝ) : ℂ) • Model.action (doeblinRemainder A π θ) f := by
  ext i
  simp only [Model.action_apply, Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext j; rw [doeblin_entry_decomposition A π θ hθ i j]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, hmean, mul_zero, zero_add]

/-- The case theta=1 is treated explicitly, without division by 1-theta. -/
theorem doeblin_one_eq_projection (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hrow : ∀ i, ∑ j, A i j = 1) (hπ : ∑ j, π j = 1)
    (hminor : ∀ i j, π j ≤ A i j) : ∀ i j, A i j = π j := by
  intro i j
  have hs : ∑ j, (A i j-π j) = 0 := by rw [Finset.sum_sub_distrib, hrow i, hπ]; ring
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sub_nonneg.mpr (hminor i j))).mp hs j (Finset.mem_univ j)
  linarith

/-- Quantitative contraction on the zero-mean subspace, including theta=1. -/
theorem doeblin_zero_mean_contraction (A : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hπ0 : ∀ i, 0 ≤ π i)
    (hrow : ∀ i, ∑ j, A i j = 1) (hπ : ∑ j, π j = 1)
    (hstat : ∀ j, ∑ i, π i*A i j = π j)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hminor : ∀ i j, θ*π j ≤ A i j)
    (f : ι → ℂ) (hmean : ∑ i, (π i : ℂ)*f i = 0) :
    weightedNorm π (Model.action A f) ≤ (1-θ)*weightedNorm π f := by
  rcases lt_or_eq_of_le hθ1 with hθ | rfl
  · rw [doeblin_zero_mean_identity A π θ hθ f hmean, weightedNorm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-θ)]
    exact mul_le_mul_of_nonneg_left
      (markov_weightedNorm_contraction (doeblinRemainder A π θ) π
        (doeblin_nonnegative A π θ hθ hminor) hπ0
        (doeblin_stochastic A π θ hθ hrow hπ)
        (doeblin_stationary A π θ hθ hstat hπ) f) (by linarith)
  · have he := doeblin_one_eq_projection A π hrow hπ (by simpa using hminor)
    have hz : Model.action A f = 0 := by ext i; simpa [Model.action_apply, he] using hmean
    simp [hz, weightedNorm_zero]

/-- The algebraic telescoping identity used in the mixing-space proof. -/
theorem linear_power_telescope (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (L : ℕ) (f : ι → ℂ) :
    f-(T^L) f = ∑ j ∈ Finset.range L, (T^j) (f-T f) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ, Module.End.mul_apply, map_sub]
    abel

theorem weightedNorm_power_contraction (π : ι → ℝ)
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hT : ∀ f, weightedNorm π (T f) ≤ weightedNorm π f)
    (L : ℕ) (f : ι → ℂ) : weightedNorm π ((T^L) f) ≤ weightedNorm π f := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hT _).trans ih

theorem weightedNorm_power_residual (π : ι → ℝ)
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hT : ∀ f, weightedNorm π (T f) ≤ weightedNorm π f)
    (L : ℕ) (f : ι → ℂ) :
    weightedNorm π (f-(T^L) f) ≤ (L : ℝ)*weightedNorm π (f-T f) := by
  rw [linear_power_telescope]
  calc
    _ ≤ ∑ j ∈ Finset.range L, weightedNorm π ((T^j) (f-T f)) :=
      weightedNorm_sum_le π _ _
    _ ≤ ∑ _j ∈ Finset.range L, weightedNorm π (f-T f) :=
      Finset.sum_le_sum (fun j _ => weightedNorm_power_contraction π T hT j _)
    _ = _ := by simp

/-- A strict contraction of one power gives the source's one-step lower
bound; the proof is the reverse triangle inequality and geometric sum. -/
theorem weightedNorm_gap_of_power_contraction (π : ι → ℝ)
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (hT : ∀ f, weightedNorm π (T f) ≤ weightedNorm π f)
    (L : ℕ) (hL : 0 < L) (θ : ℝ) (f : ι → ℂ)
    (hpower : weightedNorm π ((T^L) f) ≤ (1-θ)*weightedNorm π f) :
    (θ/(L : ℝ))*weightedNorm π f ≤ weightedNorm π (f-T f) := by
  have hr := weightedNorm_sub_le π f ((T^L) f)
  have ht := weightedNorm_power_residual π T hT L f
  have hh : θ*weightedNorm π f ≤ (L : ℝ)*weightedNorm π (f-T f) := by
    nlinarith
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hLr).mpr
  simpa only [mul_comm (weightedNorm π (f-T f))] using hh

theorem smul_linear_power (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (c : ℂ) (L : ℕ) (f : ι → ℂ) :
    ((c • T)^L) f = c^L • ((T^L) f) := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.smul_apply, ih,
      map_smul, smul_smul]
    rw [mul_comm (c^L) c]

theorem action_mul (A B : Matrix ι ι ℝ) :
    Model.action (A*B) = (Model.action A)*(Model.action B) := by
  ext f i
  simp only [Model.action_apply, Module.End.mul_apply, Matrix.mul_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem action_pow [DecidableEq ι] (Q : Matrix ι ι ℝ) (L : ℕ) :
    Model.action (Q^L) = (Model.action Q)^L := by
  induction L with
  | zero =>
    apply LinearMap.ext
    intro f
    funext i
    simp [Model.action_apply, Matrix.one_apply, apply_ite, ite_mul]
  | succ L ih => rw [pow_succ, action_mul, ih, pow_succ]

/-- Exact last estimate of Step 3: a weighted contraction for Q^L implies
the uniform gap theta/L for I-lambda Q, for every 0 <= lambda <= 1. -/
theorem markov_mixing_gap [DecidableEq ι] (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hπ : ∀ i, 0 ≤ π i)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i*Q i j = π j)
    (L : ℕ) (hL : 0 < L) (θ lam : ℝ) (hθ : θ ≤ 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (f : ι → ℂ)
    (hpower : weightedNorm π (Model.action (Q^L) f) ≤ (1-θ)*weightedNorm π f) :
    (θ/(L : ℝ))*weightedNorm π f ≤
      weightedNorm π (f-(lam : ℂ) • Model.action Q f) := by
  let T := (lam : ℂ) • Model.action Q
  have hT : ∀ g, weightedNorm π (T g) ≤ weightedNorm π g := by
    intro g
    change weightedNorm π ((lam : ℂ) • Model.action Q g) ≤ _
    rw [weightedNorm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0]
    exact (mul_le_mul_of_nonneg_left
      (markov_weightedNorm_contraction Q π hQ hπ hrow hstat g) hlam0).trans
      (mul_le_of_le_one_left (weightedNorm_nonneg π g) hlam1)
  have hp : weightedNorm π ((T^L) f) ≤ (1-θ)*weightedNorm π f := by
    rw [show T = (lam : ℂ) • Model.action Q from rfl, smul_linear_power,
      weightedNorm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam0,
      ← action_pow]
    exact (mul_le_mul_of_nonneg_left hpower (pow_nonneg hlam0 _)).trans
      (mul_le_of_le_one_left (mul_nonneg (sub_nonneg.mpr hθ) (weightedNorm_nonneg π f))
        (pow_le_one₀ hlam0 hlam1))
  exact weightedNorm_gap_of_power_contraction π T hT L hL θ f hp

section Coefficient
variable [Nonempty ι]

/-- The source's exact maximal minorization coefficient. -/
def doeblinCoefficient (A : Matrix ι ι ℝ) (π : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun ij : ι × ι => A ij.1 ij.2 / π ij.2)

theorem doeblinCoefficient_minorization (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) : ∀ i j, doeblinCoefficient A π * π j ≤ A i j := by
  intro i j
  exact (le_div_iff₀ (hπ j)).mp
    (Finset.inf'_le (fun ij : ι × ι => A ij.1 ij.2 / π ij.2) (Finset.mem_univ (i,j)))

theorem doeblinCoefficient_le_one (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (hπsum : ∑ i, π i = 1)
    (hrow : ∀ i, ∑ j, A i j = 1) : doeblinCoefficient A π ≤ 1 := by
  let i : ι := Classical.choice inferInstance
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    doeblinCoefficient_minorization A π hπ i j)
  simpa only [← Finset.mul_sum, hπsum, mul_one, hrow i] using hh

theorem probability_coordinate_le_one (π : ι → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hπsum : ∑ i, π i = 1) (j : ι) : π j ≤ 1 := by
  rw [← hπsum]
  exact Finset.single_le_sum (fun i _ => hπ i) (Finset.mem_univ j)

theorem doeblinCoefficient_lower (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (hπsum : ∑ i, π i = 1)
    (κ : ℝ) (hκ : 0 ≤ κ) (hminor : ∀ i j, κ ≤ A i j) :
    κ ≤ doeblinCoefficient A π := by
  apply Finset.le_inf'
  intro ij _
  apply (le_div_iff₀ (hπ ij.2)).mpr
  exact (mul_le_of_le_one_right hκ
    (probability_coordinate_le_one π (fun i => (hπ i).le) hπsum ij.2)).trans
    (hminor ij.1 ij.2)

/-- The exact theta chosen in the source yields a contraction; its lower
bound is the common entry lower bound (in the application kappa_Q^(N*d*)). -/
theorem doeblin_coefficient_contraction (A : Matrix ι ι ℝ) (π : ι → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hπ : ∀ i, 0 < π i)
    (hrow : ∀ i, ∑ j, A i j = 1) (hπsum : ∑ j, π j = 1)
    (hstat : ∀ j, ∑ i, π i*A i j = π j)
    (κ : ℝ) (hκ : 0 ≤ κ) (hminor : ∀ i j, κ ≤ A i j)
    (f : ι → ℂ) (hmean : ∑ i, (π i : ℂ)*f i = 0) :
    κ ≤ doeblinCoefficient A π ∧ doeblinCoefficient A π ≤ 1 ∧
      weightedNorm π (Model.action A f) ≤
        (1-doeblinCoefficient A π)*weightedNorm π f := by
  have hlo := doeblinCoefficient_lower A π hπ hπsum κ hκ hminor
  have hhi := doeblinCoefficient_le_one A π hπ hπsum hrow
  exact ⟨hlo,hhi,doeblin_zero_mean_contraction A π _ hA (fun i => (hπ i).le)
    hrow hπsum hstat (hκ.trans hlo) hhi
    (doeblinCoefficient_minorization A π hπ) f hmean⟩

end Coefficient

/-- The same Doeblin construction against a class-averaging Markov matrix.
This permits simultaneous treatment of all periodic classes. -/
def doeblinRemainderAgainst (A P : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  fun i j => (A i j-θ*P i j)/(1-θ)

theorem doeblinAgainst_nonnegative (A P : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : θ < 1) (hminor : ∀ i j, θ*P i j ≤ A i j) :
    ∀ i j, 0 ≤ doeblinRemainderAgainst A P θ i j :=
  fun i j => div_nonneg (sub_nonneg.mpr (hminor i j)) (by linarith)

theorem doeblinAgainst_stochastic (A P : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : θ < 1) (hA : ∀ i, ∑ j, A i j = 1) (hP : ∀ i, ∑ j, P i j = 1) :
    ∀ i, ∑ j, doeblinRemainderAgainst A P θ i j = 1 := by
  intro i
  simp only [doeblinRemainderAgainst, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hA i, hP i, mul_one]
  exact div_self (by linarith)

theorem doeblinAgainst_stationary (A P : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hθ : θ < 1)
    (hA : ∀ j, ∑ i, π i*A i j = π j) (hP : ∀ j, ∑ i, π i*P i j = π j) :
    ∀ j, ∑ i, π i*doeblinRemainderAgainst A P θ i j = π j := by
  intro j
  simp only [doeblinRemainderAgainst, ← mul_div_assoc, ← Finset.sum_div, mul_sub,
    Finset.sum_sub_distrib]
  have he : (∑ i, π i*(θ*P i j)) = θ*π j := by
    calc
      _ = θ*∑ i, π i*P i j := by rw [Finset.mul_sum]; congr 1; ext i; ring
      _ = _ := by rw [hP j]
  rw [hA j, he]
  field_simp [show 1-θ ≠ 0 by linarith]

theorem doeblinAgainst_entry_decomposition (A P : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : θ < 1) (i j : ι) :
    A i j = θ*P i j+(1-θ)*doeblinRemainderAgainst A P θ i j := by
  unfold doeblinRemainderAgainst
  rw [mul_div_cancel₀ _ (by linarith : 1-θ ≠ 0)]
  ring

theorem doeblinAgainst_kernel_identity (A P : Matrix ι ι ℝ) (θ : ℝ)
    (hθ : θ < 1) (f : ι → ℂ) (hPf : Model.action P f = 0) :
    Model.action A f = ((1-θ : ℝ) : ℂ) • Model.action (doeblinRemainderAgainst A P θ) f := by
  ext i
  have hp : ∑ j, (P i j : ℂ)*f j = 0 := congrFun hPf i
  simp only [Model.action_apply, Pi.smul_apply, smul_eq_mul]
  conv_lhs => arg 2; ext j; rw [doeblinAgainst_entry_decomposition A P θ hθ i j]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, hp, mul_zero, zero_add]

theorem doeblinAgainst_one_eq (A P : Matrix ι ι ℝ)
    (hA : ∀ i, ∑ j, A i j = 1) (hP : ∀ i, ∑ j, P i j = 1)
    (hminor : ∀ i j, P i j ≤ A i j) : A = P := by
  ext i j
  have hs : ∑ j, (A i j-P i j) = 0 := by rw [Finset.sum_sub_distrib, hA i, hP i]; ring
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sub_nonneg.mpr (hminor i j))).mp hs j (Finset.mem_univ j)
  linarith

/-- A simultaneous classwise Doeblin contraction. In the periodic application
P is the actual class-averaging matrix, and P f=0 means zero mean in each class. -/
theorem doeblinAgainst_kernel_contraction (A P : Matrix ι ι ℝ) (π : ι → ℝ) (θ : ℝ)
    (hπ0 : ∀ i, 0 ≤ π i)
    (hArow : ∀ i, ∑ j, A i j = 1) (hProw : ∀ i, ∑ j, P i j = 1)
    (hAstat : ∀ j, ∑ i, π i*A i j = π j) (hPstat : ∀ j, ∑ i, π i*P i j = π j)
    (hθ1 : θ ≤ 1) (hminor : ∀ i j, θ*P i j ≤ A i j)
    (f : ι → ℂ) (hPf : Model.action P f = 0) :
    weightedNorm π (Model.action A f) ≤ (1-θ)*weightedNorm π f := by
  rcases lt_or_eq_of_le hθ1 with hθ | rfl
  · rw [doeblinAgainst_kernel_identity A P θ hθ f hPf, weightedNorm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-θ)]
    exact mul_le_mul_of_nonneg_left
      (markov_weightedNorm_contraction (doeblinRemainderAgainst A P θ) π
        (doeblinAgainst_nonnegative A P θ hθ hminor) hπ0
        (doeblinAgainst_stochastic A P θ hθ hArow hProw)
        (doeblinAgainst_stationary A P π θ hθ hAstat hPstat) f) (by linarith)
  · have he := doeblinAgainst_one_eq A P hArow hProw (by simpa using hminor)
    simp [he, hPf, weightedNorm_zero]

theorem weightedSquare_euclidean_bounds (π : ι → ℝ) (a b : ℝ)
    (hlo : ∀ i, a ≤ π i) (hhi : ∀ i, π i ≤ b) (f : ι → ℂ) :
    a*‖WithLp.toLp 2 f‖^2 ≤ weightedSquare π f ∧
      weightedSquare π f ≤ b*‖WithLp.toLp 2 f‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, weightedSquare, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hlo i) (sq_nonneg _))
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hhi i) (sq_nonneg _))

/-- The source's comparison between weighted and Euclidean L² norms. -/
theorem weightedNorm_euclidean_bounds (π : ι → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlo : ∀ i, a ≤ π i) (hhi : ∀ i, π i ≤ b)
    (f : ι → ℂ) :
    Real.sqrt a*‖WithLp.toLp 2 f‖ ≤ weightedNorm π f ∧
      weightedNorm π f ≤ Real.sqrt b*‖WithLp.toLp 2 f‖ := by
  have hπ : ∀ i, 0 ≤ π i := fun i => ha.trans (hlo i)
  obtain ⟨hl,hh⟩ := weightedSquare_euclidean_bounds π a b hlo hhi f
  rw [← weightedNorm_sq π hπ] at hl hh
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hn := weightedNorm_nonneg π f
  have hna := mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg (WithLp.toLp 2 f))
  have hnb := mul_nonneg (Real.sqrt_nonneg b) (norm_nonneg (WithLp.toLp 2 f))
  constructor <;> nlinarith

end NonSymmetricDyson.Paper.Perron
