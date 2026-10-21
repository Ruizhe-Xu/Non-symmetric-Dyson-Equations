import Dyson.Full.Singularities
import Dyson.Full.PerronIdentity

/-! The paper's cubic coefficient is nonnegative also away from the frontier,
where the Perron eigenvalue is below one and σ need not vanish. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.Singularities
variable {ι : Type*} [Fintype ι]

/-- Orthogonality removes the projected σ-term from the actual quadratic
form, including moving Perron eigenvalues. -/
theorem cubicCoefficient_eq_variance_projected
    (F : ι → ι → ℝ) (p l r u : ι → ℝ) (lam σ : ℝ)
    (hr : ∀ i,r i≠0) (hlF : ∀ j,∑ i,l i*F i j=lam*l j)
    (horth : ∑ i,l i*u i=0)
    (hu : ∀ i,u i-∑ j,F i j*u j=p i*r i^2-σ*r i) :
    cubicCoefficient F p l r u =
      (∑ i,stationaryWeight l r i*(u i/r i)^2)-
      (∑ i,stationaryWeight l r i*((∑ j,F i j*u j)/r i)^2) := by
  have horthF : ∑ i,l i*(∑ j,F i j*u j)=0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,hlF,mul_assoc]
    rw [← Finset.mul_sum,horth,mul_zero]
  have hzero : ∑ i,σ*l i*(u i+∑ j,F i j*u j)=0 := by
    simp_rw [mul_assoc,← Finset.mul_sum,mul_add,Finset.sum_add_distrib]
    rw [horth,horthF]
    ring
  have hterm (i : ι) : p i*l i*r i*(u i+∑ j,F i j*u j)=
      stationaryWeight l r i*(u i/r i)^2-
      stationaryWeight l r i*((∑ j,F i j*u j)/r i)^2+
      σ*l i*(u i+∑ j,F i j*u j) := by
    dsimp [stationaryWeight]
    have hi := hu i
    field_simp [hr i]
    linear_combination -(l i*(u i+∑ j,F i j*u j))*hi
  unfold cubicCoefficient
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hzero,add_zero]

/-- Jensen's inequality for the actual moving Perron data proves ψ≥0
for every positive Perron eigenvalue at most one. -/
theorem cubicCoefficient_nonnegative_projected
    (F : ι → ι → ℝ) (p l r u : ι → ℝ) (lam σ : ℝ)
    (hF : ∀ i j,0≤F i j) (hl : ∀ i,0<l i) (hr : ∀ i,0<r i)
    (hlam : 0<lam) (hlam1 : lam≤1)
    (hFr : ∀ i,∑ j,F i j*r j=lam*r i)
    (hlF : ∀ j,∑ i,l i*F i j=lam*l j)
    (horth : ∑ i,l i*u i=0)
    (hu : ∀ i,u i-∑ j,F i j*u j=p i*r i^2-σ*r i) :
    0≤cubicCoefficient F p l r u := by
  let G : ι → ι → ℝ := fun i j => F i j/lam
  have hG : ∀ i j,0≤G i j := fun i j => div_nonneg (hF i j) hlam.le
  have hGr : ∀ i,∑ j,G i j*r j=r i := by
    intro i
    simp only [G,div_mul_eq_mul_div,← Finset.sum_div,hFr]
    field_simp
  have hlG : ∀ j,∑ i,l i*G i j=l j := by
    intro j
    simp only [G,← mul_div_assoc,← Finset.sum_div,hlF]
    field_simp
  have hc := stationary_contraction_nonnegative
    (markovKernel G r) (stationaryWeight l r) (fun i => u i/r i)
    (fun i => (∑ j,G i j*u j)/r i)
    (fun i j => div_nonneg (mul_nonneg (hG i j) (hr j).le) (hr i).le)
    (fun i => (mul_pos (hl i) (hr i)).le)
    (markovKernel_row_sum G r (fun i => (hr i).ne') hGr)
    (stationaryWeight_stationary G l r (fun i => (hr i).ne') hlG)
    (markovKernel_mean G r u (fun i => (hr i).ne')) lam hlam.le hlam1
  rw [cubicCoefficient_eq_variance_projected F p l r u lam σ
    (fun i => (hr i).ne') hlF horth hu]
  have he : lam^2*(∑ i,stationaryWeight l r i*((∑ j,G i j*u j)/r i)^2)=
      ∑ i,stationaryWeight l r i*((∑ j,F i j*u j)/r i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [G,div_mul_eq_mul_div,← Finset.sum_div]
    field_simp
    <;> ring
  rwa [he] at hc

end NonSymmetricDyson.Full.Singularities
