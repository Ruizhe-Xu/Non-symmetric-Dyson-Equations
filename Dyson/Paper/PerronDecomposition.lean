import Dyson.Paper.PerronPeriodic

/-! Original orthogonal decomposition into the period subspace and the
classwise centered mixing subspace. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open Finset
namespace NonSymmetricDyson.Paper.Perron
variable {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]

def classAverage (π : ι → ℝ) (cls : ι → ZMod p) (x : ι → ℂ) : ι → ℂ :=
  fun i => (p:ℂ)*classMean π cls (cls i) x

theorem sum_classMean (π : ι → ℝ) (cls : ι → ZMod p) (x : ι → ℂ) :
    ∑ c, classMean π cls c x = ∑ i, (π i:ℂ)*x i := by
  unfold classMean
  rw [Finset.sum_comm]
  simp

theorem classMean_classConstant (π : ι → ℝ) (cls : ι → ZMod p)
    (a : ZMod p → ℂ) (c : ZMod p) :
    classMean π cls c (fun i => a (cls i))=(classMass π cls c:ℂ)*a c := by
  simp only [classMean, classMass, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : cls i=c <;> simp [hi]

theorem classAverage_constant (π : ι → ℝ) (cls : ι → ZMod p) (x : ι → ℂ) :
    ClassConstant cls (classAverage π cls x) :=
  ⟨fun c => (p:ℂ)*classMean π cls c x, fun _ => rfl⟩

theorem classMean_sub (π : ι → ℝ) (cls : ι → ZMod p) (c : ZMod p) (x y : ι → ℂ) :
    classMean π cls c (x-y)=classMean π cls c x-classMean π cls c y := by
  simp only [classMean, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem classMean_classAverage (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (x : ι → ℂ) (c : ZMod p) :
    classMean π cls c (classAverage π cls x)=classMean π cls c x := by
  unfold classAverage
  rw [classMean_classConstant π cls (fun b => (p:ℂ)*classMean π cls b x) c, hmass]
  simp [mul_assoc, NeZero.ne p]

theorem classCentered_remainder (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (x : ι → ℂ) :
    ClassCentered π cls (x-classAverage π cls x) := by
  intro c
  rw [classMean_sub, classMean_classAverage π cls hmass, sub_self]

theorem classAverage_preserves_mean (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (x : ι → ℂ) :
    (∑ i, (π i:ℂ)*classAverage π cls x i)=∑ i, (π i:ℂ)*x i := by
  rw [← sum_classMean π cls, ← sum_classMean π cls x]
  apply Finset.sum_congr rfl
  intro c _
  exact classMean_classAverage π cls hmass x c

theorem weightedInner_classConstant (π : ι → ℝ) (cls : ι → ZMod p)
    (a : ZMod p → ℂ) (x : ι → ℂ) :
    weightedInner π (fun i => a (cls i)) x =
      ∑ c, conj (a c)*classMean π cls c x := by
  unfold weightedInner classMean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem classCentered_orthogonal (π : ι → ℝ) (cls : ι → ZMod p)
    (u v : ι → ℂ) (hu : ClassConstant cls u) (hv : ClassCentered π cls v) :
    weightedInner π u v=0 := by
  obtain ⟨a, ha⟩ := hu
  have heu : u=fun i => a (cls i) := funext ha
  rw [heu, weightedInner_classConstant]
  change ∀ c, classMean π cls c v=0 at hv
  simp [hv]

/-- The explicit orthogonal decomposition used in Steps 3 and 4. If the
input has total mean zero, its periodic part has total mean zero as well. -/
theorem periodic_mixing_decomposition (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (x : ι → ℂ) :
    ∃ u v : ι → ℂ, x=u+v ∧ ClassConstant cls u ∧ ClassCentered π cls v ∧
      weightedInner π u v=0 ∧
      (∑ i, (π i:ℂ)*u i)=∑ i, (π i:ℂ)*x i := by
  refine ⟨classAverage π cls x, x-classAverage π cls x, ?_,
    classAverage_constant π cls x, classCentered_remainder π cls hmass x, ?_,
    classAverage_preserves_mean π cls hmass x⟩
  · abel
  · exact classCentered_orthogonal π cls _ _ (classAverage_constant π cls x)
      (classCentered_remainder π cls hmass x)

theorem weightedInner_sum_left {κ : Type*} [Fintype κ] (π : ι → ℝ)
    (a : κ → ℂ) (e : κ → ι → ℂ) (y : ι → ℂ) :
    weightedInner π (∑ k, a k • e k) y =
      ∑ k, conj (a k)*weightedInner π (e k) y := by
  simp only [weightedInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedInner_sum_right {κ : Type*} [Fintype κ] (π : ι → ℝ)
    (a : κ → ℂ) (e : κ → ι → ℂ) (x : ι → ℂ) :
    weightedInner π x (∑ k, a k • e k) =
      ∑ k, a k*weightedInner π x (e k) := by
  simp only [weightedInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Parseval on the original period subspace, from the explicitly proved
weighted orthonormality rather than an assumed Fourier diagonalization. -/
theorem periodVector_parseval (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (a : ZMod p → ℂ) :
    weightedInner π (∑ k, a k • periodVector cls k)
      (∑ k, a k • periodVector cls k) = ∑ k, conj (a k)*a k := by
  rw [weightedInner_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedInner_sum_right]
  simp [periodVector_orthonormal π cls hmass]

theorem mean_periodVector (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (k : ZMod p) :
    (∑ i, (π i:ℂ)*periodVector cls k i)=if k=0 then 1 else 0 := by
  have h := periodVector_orthonormal π cls hmass 0 k
  simpa [weightedInner, periodVector, eq_comm] using h

theorem mean_fourier_coefficients (π : ι → ℝ) (cls : ι → ZMod p)
    (hmass : ∀ c, classMass π cls c=(p:ℝ)⁻¹) (a : ZMod p → ℂ) :
    (∑ i, (π i:ℂ)*(∑ k, a k • periodVector cls k) i)=a 0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k, a k*(∑ i, (π i:ℂ)*periodVector cls k i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a 0 := by simp [mean_periodVector π cls hmass]

end NonSymmetricDyson.Paper.Perron
