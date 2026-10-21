import Dyson.Full.SpectralExpansion
import Dyson.Full.SpectralEuclidean

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Spectral Singularities
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem norm_square_mul_phase (m : ℂ) (hm : m≠0) :
    m^2*(star m/m)=(‖m‖:ℂ)^2 := by
  calc
    m^2*(star m/m)=m*star m := by field_simp <;> ring
    _ = (Complex.normSq m:ℂ) := Complex.mul_conj m
    _ = (‖m‖:ℂ)^2 := by rw [Complex.normSq_eq_norm_sq]; push_cast; rfl

theorem reduced_stability_identity (S : Matrix ι ι ℝ) (m : ι → ℂ)
    (hm : ∀ i, m i≠0) (x : ι → ℂ) (i : ι) :
    InteriorStability.stabilityOperator S m (fun j => (‖m j‖:ℂ)*x j) i =
      ((m i)^2/(‖m i‖:ℂ))*reducedOperator S m x i := by
  have hq : (‖m i‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr (hm i)
  have hp : ((m i)^2/(‖m i‖:ℂ))*(star (m i)/m i)=(‖m i‖:ℂ) := by
    rw [div_mul_eq_mul_div, norm_square_mul_phase _ (hm i)]
    field_simp
  have hs : saturatedOperator S m x i =
      (‖m i‖:ℂ)*∑ j, (S i j:ℂ)*(‖m j‖:ℂ)*x j := by
    simp only [saturatedOperator,complexMatrixOperator_apply,Complex.ofReal_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (‖m i‖:ℂ)*x i-(m i)^2*(∑ j, (S i j:ℂ)*((‖m j‖:ℂ)*x j)) =
    ((m i)^2/(‖m i‖:ℂ))*((star (m i)/m i)*x i-saturatedOperator S m x i)
  rw [hs,mul_sub,← mul_assoc,hp]
  congr 1
  rw [← mul_assoc, div_mul_cancel₀ _ hq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reduced_injective_upper (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m) :
    Function.Injective (reducedOperator S m) := by
  have hnz : ∀ i, m i≠0 := fun i h => by simpa [h] using hm i
  have hker : ∀ x, reducedOperator S m x=0 → x=0 := by
    intro x hx
    have hh : InteriorStability.stabilityOperator S m (fun j => (‖m j‖:ℂ)*x j)=0 := by
      ext i
      rw [reduced_stability_identity S m hnz x i,hx]
      simp
    have hzq : (fun j => (‖m j‖:ℂ)*x j)=0 :=
      InteriorStability.stability_injective hS hz hm heq (by simpa using hh)
    ext i
    have hi := congrFun hzq i
    have hq : (‖m i‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr (hnz i)
    exact (mul_eq_zero.mp hi).resolve_left hq
  intro x y hxy
  have hh : reducedOperator S m (x-y)=0 := by rw [map_sub,hxy,sub_self]
  exact sub_eq_zero.mp (hker _ hh)

theorem spectral_value_ne_zero_upper (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j, 0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (d : SimpleSpectralSplit (reducedOperator S m)) : d.value≠0 := by
  intro h
  have hh := d.right_eigen
  rw [h,zero_smul] at hh
  exact d.right_ne_zero (reduced_injective_upper S a z m hS hz hm heq (by simpa using hh))

theorem spectral_value_zero_of_kernel {A : End ι} (d : SimpleSpectralSplit A)
    (r : Vec ι) (hr : r≠0) (hAr : A r=0) : d.value=0 := by
  by_contra h
  have hh := d.inverse_left h r
  rw [hAr,map_zero] at hh
  exact hr hh.symm

end NonSymmetricDyson.Full.SingularSpectral
