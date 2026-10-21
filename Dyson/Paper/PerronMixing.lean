import Dyson.Paper.PerronDecomposition
import Dyson.Paper.PerronDoeblin

/-! Original periodic-class Doeblin application to the actual matrix power.
The minorization is proved against the class-averaging projector. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.Perron
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [NeZero p]

theorem power_nonnegative (Q : Matrix ι ι ℝ) (hQ : ∀ i j,0≤Q i j) (L : ℕ) :
    ∀ i j,0≤(Q^L) i j := by
  induction L with
  | zero => intro i j; simp only [pow_zero,Matrix.one_apply]; split <;> norm_num
  | succ L ih =>
    intro i j
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hQ k j))

theorem power_stochastic (Q : Matrix ι ι ℝ) (hrow : ∀ i,∑ j,Q i j=1) (L : ℕ) :
    ∀ i,∑ j,(Q^L) i j=1 := by
  induction L with
  | zero => intro i; simp [Matrix.one_apply]
  | succ L ih =>
    intro i
    simp only [pow_succ,Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,hrow,mul_one,ih]

theorem power_stationary (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (hstat : ∀ j,∑ i,π i*Q i j=π j) (L : ℕ) :
    ∀ j,∑ i,π i*(Q^L) i j=π j := by
  induction L with
  | zero => intro j; simp [Matrix.one_apply]
  | succ L ih =>
    intro j
    simp only [pow_succ,Matrix.mul_apply,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,ih,hstat]

def classProjection (π : ι → ℝ) (cls : ι → ZMod p) : Matrix ι ι ℝ :=
  fun i j => if cls j=cls i then (p:ℝ)*π j else 0

theorem classProjection_nonnegative (π : ι → ℝ) (hπ : ∀ i,0≤π i) (cls : ι → ZMod p) :
    ∀ i j,0≤classProjection π cls i j := by
  intro i j
  unfold classProjection
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg p) (hπ j)
  · exact le_rfl

theorem classProjection_stochastic (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹) :
    ∀ i,∑ j,classProjection π cls i j=1 := by
  intro i
  have he : (∑ j,classProjection π cls i j)=(p:ℝ)*classMass π cls (cls i) := by
    simp [classProjection,classMass,Finset.mul_sum,mul_ite]
  rw [he,hmass]
  simp [NeZero.ne p]

theorem classProjection_stationary (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹) :
    ∀ j,∑ i,π i*classProjection π cls i j=π j := by
  intro j
  have he : (∑ i,π i*classProjection π cls i j)=
      classMass π cls (cls j)*((p:ℝ)*π j) := by
    simp only [classProjection,classMass,Finset.sum_mul,mul_ite,ite_mul,zero_mul,mul_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp [eq_comm]
  rw [he,hmass]
  simp [mul_assoc,NeZero.ne p]

theorem classProjection_action (π : ι → ℝ) (cls : ι → ZMod p) (x : ι → ℂ) :
    Model.action (classProjection π cls) x=classAverage π cls x := by
  ext i
  simp [Model.action_apply,classProjection,classAverage,classMean,Finset.mul_sum,
    apply_ite,ite_mul,mul_ite,mul_assoc]

theorem classProjection_kills_centered (π : ι → ℝ) (cls : ι → ZMod p)
    (x : ι → ℂ) (hx : ClassCentered π cls x) :
    Model.action (classProjection π cls) x=0 := by
  rw [classProjection_action]
  ext i
  exact mul_eq_zero_of_right _ (hx (cls i))

/-- Any strictly positive same-class power gives the original simultaneous
Doeblin minorization. No power contraction is assumed. -/
theorem class_power_minorization (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (cls : ι → ZMod p) (hQ : ∀ i j,0≤Q i j) (hπ : ∀ i,0≤π i)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹)
    (L : ℕ) (θ : ℝ) (hθ : 0≤θ)
    (hpower : ∀ i j,cls i=cls j → θ≤(Q^L) i j) :
    ∀ i j,θ*classProjection π cls i j≤(Q^L) i j := by
  intro i j
  have hp := classProjection_nonnegative π hπ cls
  have hrow := classProjection_stochastic π cls hmass
  by_cases hij : cls j=cls i
  · have hle : classProjection π cls i j≤1 := by
      rw [← hrow i]
      exact Finset.single_le_sum (fun k _ => hp i k) (Finset.mem_univ j)
    exact (mul_le_of_le_one_right hθ hle).trans (hpower i j hij.symm)
  · simp only [classProjection,hij,if_false,mul_zero]
    exact power_nonnegative Q hQ L i j

theorem class_centered_power_contraction (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (cls : ι → ZMod p) (hQ : ∀ i j,0≤Q i j) (hπ : ∀ i,0≤π i)
    (hrow : ∀ i,∑ j,Q i j=1) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹)
    (L : ℕ) (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1)
    (hpower : ∀ i j,cls i=cls j → θ≤(Q^L) i j)
    (x : ι → ℂ) (hx : ClassCentered π cls x) :
    weightedNorm π (Model.action (Q^L) x)≤(1-θ)*weightedNorm π x :=
  doeblinAgainst_kernel_contraction (Q^L) (classProjection π cls) π θ hπ
    (power_stochastic Q hrow L) (classProjection_stochastic π cls hmass)
    (power_stationary Q π hstat L) (classProjection_stationary π cls hmass) hθ1
    (class_power_minorization Q π cls hQ hπ hmass L θ hθ hpower) x
    (classProjection_kills_centered π cls x hx)

/-- Original Step 3's final θ/L gap, now applied to the actual cyclic-class
projector and actual stochastic power. -/
theorem class_centered_gap (Q : Matrix ι ι ℝ) (π : ι → ℝ)
    (cls : ι → ZMod p) (hQ : ∀ i j,0≤Q i j) (hπ : ∀ i,0≤π i)
    (hrow : ∀ i,∑ j,Q i j=1) (hstat : ∀ j,∑ i,π i*Q i j=π j)
    (hmass : ∀ c,classMass π cls c=(p:ℝ)⁻¹)
    (L : ℕ) (hL : 0<L) (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1)
    (hpower : ∀ i j,cls i=cls j → θ≤(Q^L) i j)
    (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (x : ι → ℂ) (hx : ClassCentered π cls x) :
    (θ/(L:ℝ))*weightedNorm π x≤weightedNorm π (x-(lam:ℂ) • Model.action Q x) :=
  markov_mixing_gap Q π hQ hπ hrow hstat L hL θ lam hθ1 hlam hlam1 x
    (class_centered_power_contraction Q π cls hQ hπ hrow hstat hmass L θ hθ hθ1 hpower x hx)

end NonSymmetricDyson.Paper.Perron
