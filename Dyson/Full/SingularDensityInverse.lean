import Dyson.Full.SingularPhysicalInverse
import Dyson.Full.SpectralInvertibility

/-! The original intermediate inverse bound by inverse squared density,
derived from the actual physical edge/cusp chart and diagonal conjugation. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.SingularLinear
open Singularities ExternalAlgebraic
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual total imaginary part is bounded linearly in the physical
monomial parameter; the center value is real. -/
theorem physical_normal_form_density_parameter_bound
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ} {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (nf : PhysicalNormalForm S a τ m m₀) :
    ∃ H : ℝ,0<H ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),
      (∑ i,(m z i).im)≤H*‖nf.parameter z‖ := by
  let H : ℝ := ∑ i,(|nf.tangent i|+nf.errorConstant)
  have hH : 0<H := Finset.sum_pos (fun i _ => add_pos_of_nonneg_of_pos (abs_nonneg _) nf.errorConstant_pos) Finset.univ_nonempty
  have hsmall : ∀ᶠ z in 𝓝[upper] (τ:ℂ), ‖nf.parameter z‖≤1 :=
    nf.parameter_limit.norm.eventually_le_const (by norm_num)
  refine ⟨H,hH,?_⟩
  filter_upwards [nf.physical,nf.parameter_limit.eventually nf.taylor,hsmall] with z hz ht hs
  obtain ⟨hm,_,_⟩ := hz
  rw [hm]
  have hterm (i : ι) : (nf.curve (nf.parameter z) i).im≤
      (|nf.tangent i|+nf.errorConstant)*‖nf.parameter z‖ := by
    have hni : (nf.curve (nf.parameter z) i).im≤
        ‖nf.curve (nf.parameter z) i-(m₀ i:ℂ)‖ := by
      simpa using (Complex.im_le_norm (nf.curve (nf.parameter z) i-(m₀ i:ℂ)))
    have htriangle := norm_add_le
      (nf.curve (nf.parameter z) i-(m₀ i:ℂ)-(nf.tangent i:ℂ)*nf.parameter z)
      ((nf.tangent i:ℂ)*nf.parameter z)
    rw [sub_add_cancel] at htriangle
    have hlin : ‖(nf.tangent i:ℂ)*nf.parameter z‖=|nf.tangent i| *‖nf.parameter z‖ := by simp
    have hb := hni.trans (htriangle.trans (add_le_add_right (ht i) _))
    rw [hlin] at hb
    nlinarith [nf.errorConstant_pos,mul_nonneg (norm_nonneg (nf.parameter z))
      (sub_nonneg.mpr hs)]
  calc
    _ ≤ ∑ i,(|nf.tangent i|+nf.errorConstant)*‖nf.parameter z‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by rw [← Finset.sum_mul]

theorem density_inverse_arithmetic (k : ℕ) (hk : k=2 ∨ k=3)
    (A ρ s C D H : ℝ) (hA : 0≤A) (hρ : 0≤ρ) (hs : 0<s) (hs1 : s≤1)
    (hC : 0<C) (hD : 0<D) (hH : 0<H)
    (hinv : A≤C/(D*s^(k-1))) (hdensity : ρ≤H*s) :
    A*ρ^2≤C*H^2/D := by
  have hsq : ρ^2≤(H*s)^2 := by nlinarith
  have hmul := mul_le_mul hinv hsq (sq_nonneg ρ) (by positivity : 0≤C/(D*s^(k-1)))
  rcases hk with rfl | rfl
  · have he : (C/(D*s^(2-1)))*(H*s)^2=(C*H^2/D)*s := by norm_num; field_simp <;> ring
    rw [he] at hmul
    exact hmul.trans (mul_le_of_le_one_right (by positivity) hs1)
  · have he : (C/(D*s^(3-1)))*(H*s)^2=C*H^2/D := by norm_num; field_simp <;> ring
    rwa [he] at hmul

/-- The actual Euclidean stability inverse obeys the density-squared bound
near both regular edges and regular cusps. -/
theorem regular_frontier_density_inverse
    (perron : ExternalPerronExistence) {n : ℕ} (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (nf : PhysicalNormalForm S a τ m (fun j => (Boundary.boundaryVector m (τ:ℂ) j).re)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀ hz:0<z.im,
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖*
        (∑ j,(m z j).im)^2≤C := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨c,C,_,hC,hbound⟩ := regular_frontier_normal_form_inverse perron hn algebraic puiseux
    S a hS hirr m hupper heq τ i hfront hτ nf
  obtain ⟨H,hH,hdensity⟩ := physical_normal_form_density_parameter_bound nf
  let D : ℝ := ‖(nf.coefficient:ℂ)‖^inverseExponent nf.degree
  have hD : 0<D := Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr nf.coefficient_ne_zero)) _
  have hsmall : ∀ᶠ z in 𝓝[upper] (τ:ℂ), ‖nf.parameter z‖≤1 :=
    nf.parameter_limit.norm.eventually_le_const (by norm_num)
  refine ⟨C*H^2/D,by positivity,?_⟩
  filter_upwards [hbound,hdensity,nf.physical,hsmall] with z hb hd hp hs1
  intro hz
  have hs : 0<‖nf.parameter z‖ := norm_pos_iff.mpr
    (fun he => by simpa [he] using hp.2.2)
  have hscale : ‖z-(τ:ℂ)‖^inverseExponent nf.degree=D*‖nf.parameter z‖^(nf.degree-1) := by
    rw [hp.2.1]
    exact monomial_norm_power _ _ _ (by rcases nf.degree_cases with h|h <;> omega)
  have hbi := (hb hz).2
  rw [hscale] at hbi
  exact density_inverse_arithmetic nf.degree nf.degree_cases _ _ _ C D H (norm_nonneg _)
    (Finset.sum_nonneg (fun j _ => (hupper z hz j).le)) hs hs1 hC hD hH hbi hd

end NonSymmetricDyson.Full.SingularLinear
