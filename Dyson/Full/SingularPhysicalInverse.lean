import Dyson.Full.SingularInverse
import Dyson.Full.SingularitiesMatching
import Dyson.Full.PerronExistence
import Dyson.Full.BoundaryEdges

noncomputable section
open scoped Topology BigOperators
open Filter Set

namespace NonSymmetricDyson.Full.SingularLinear

open Singularities ExternalAlgebraic

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def inverseExponent (k : ℕ) : ℝ := ((k-1 : ℕ) : ℝ) / (k : ℝ)

theorem monomial_norm_power (c s : ℂ) (k : ℕ) (hk : 0 < k) :
    ‖c*s^k‖ ^ inverseExponent k = ‖c‖ ^ inverseExponent k * ‖s‖^(k-1) := by
  rw [norm_mul, norm_pow, Real.mul_rpow (norm_nonneg _) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have he : (k : ℝ) * inverseExponent k = ((k-1 : ℕ) : ℝ) := by
    unfold inverseExponent
    field_simp
  rw [he, Real.rpow_natCast]

theorem positive_functional_ne_zero (l v : ι → ℝ)
    (hl : ∀ i, 0 < l i) (hv : ∀ i, 0 < v i) :
    complexFunctional l (fun i => (v i : ℂ)) ≠ 0 := by
  have hp : 0 < (complexFunctional l (fun i => (v i : ℂ))).re := by
    have hs : 0 < ∑ i, l i*v i :=
      Finset.sum_pos (fun i _ => mul_pos (hl i) (hv i)) Finset.univ_nonempty
    simpa only [complexFunctional_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      Complex.ofReal_re] using hs
  intro he
  simpa [he] using hp

/-- Positive left Perron data detect the actual positive real tangent and
squared boundary vector. The normalization required by deflation is
constructed, not included as a stability hypothesis. -/
theorem positive_tangent_kernel_data
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (q r l v : ι → ℝ)
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hq : ∀ i, 0 < q i) (hl : ∀ i, 0 < l i) (hv : ∀ i, 0 < v i)
    (hsq : ∀ i, (m i)^2 = (q i : ℂ)^2)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator (fun i => (q i : ℂ)) (Model.action S) h)
    (hlF : ∀ x, complexFunctional l (F x) = complexFunctional l x)
    (hsimple : ∀ x, F x = x → x = complexFunctional l x • (fun i => (r i : ℂ)))
    (hkernel : stabilityCLM S m (fun i => (v i : ℂ)) = 0) :
    ∃ φ : (ι → ℂ) →L[ℂ] ℂ,
      φ (fun i => (v i : ℂ)) = 1 ∧ φ (fun i => (m i)^2) ≠ 0 ∧
      (∀ x, φ (stabilityCLM S m x) = 0) ∧
      (∀ x, stabilityCLM S m x = 0 → x = φ x • (fun i => (v i : ℂ))) := by
  let qC : ι → ℂ := fun i => (q i : ℂ)
  let φ₀ := (complexFunctional l).comp (coordinateDivision qC)
  have hφ₀ (x) : φ₀ x = complexFunctional l (coordinateDivision qC x) := rfl
  have hq0 : ∀ i, qC i ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (hq i).ne'
  have hleft : ∀ x, φ₀ (stabilityCLM S m x) = 0 := by
    intro x
    rw [hφ₀, normalized_stability_identity S m qC F hq0 hsq hF, map_sub, hlF, sub_self]
  have hsimple₀ : ∀ x, stabilityCLM S m x = 0 →
      x = φ₀ x • (fun i => qC i*(r i : ℂ)) := by
    intro x hx
    have he := normalized_stability_identity S m qC F hq0 hsq hF x
    rw [hx, map_zero] at he
    have hfix : F (coordinateDivision qC x) = coordinateDivision qC x :=
      (sub_eq_zero.mp he.symm).symm
    have hs := hsimple (coordinateDivision qC x) hfix
    funext i
    have hh := congrFun hs i
    simp only [coordinateDivision_apply, Pi.smul_apply, smul_eq_mul] at hh
    have hmul := (div_eq_iff (hq0 i)).mp hh
    change x i = φ₀ x * (qC i*(r i : ℂ))
    rw [hφ₀]
    linear_combination hmul
  have hdv : coordinateDivision qC (fun i => (v i : ℂ)) =
      (fun i => ((v i/q i : ℝ) : ℂ)) := by
    funext i
    simp [coordinateDivision_apply, qC]
  have hdb : coordinateDivision qC (fun i => (m i)^2) = qC := by
    funext i
    rw [coordinateDivision_apply, hsq i]
    dsimp [qC]
    field_simp
  have hφv : φ₀ (fun i => (v i : ℂ)) ≠ 0 := by
    rw [hφ₀, hdv]
    exact positive_functional_ne_zero l (fun i => v i/q i) hl (fun i => div_pos (hv i) (hq i))
  have hφb : φ₀ (fun i => (m i)^2) ≠ 0 := by
    rw [hφ₀, hdb]
    exact positive_functional_ne_zero l q hl hq
  exact renormalize_kernel_direction (stabilityCLM S m) φ₀
    (fun i => qC i*(r i : ℂ)) (fun i => (v i : ℂ)) (fun i => (m i)^2)
    hleft hsimple₀ hkernel hφv hφb

/-- Transfer the parameter estimate to the original spectral variable by
actual physical matching in the constructed analytic monomial chart. -/
theorem physical_normal_form_inverse_of_kernel
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ) (m : ℂ → ι → ℂ) (m₀ : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (nf : PhysicalNormalForm S a τ m m₀)
    (φ : (ι → ℂ) →L[ℂ] ℂ)
    (hnorm : φ (deriv nf.curve 0) = 1)
    (hopen : φ (fun i => (nf.curve 0 i)^2) ≠ 0)
    (hleft : ∀ x, φ (stabilityCLM S (nf.curve 0) x) = 0)
    (hsimple : ∀ x, stabilityCLM S (nf.curve 0) x = 0 → x = φ x • deriv nf.curve 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ z in 𝓝[upper] (τ : ℂ), ∀ hz : 0 < z.im,
      c / ‖z-(τ : ℂ)‖ ^ inverseExponent nf.degree ≤
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
        C / ‖z-(τ : ℂ)‖ ^ inverseExponent nf.degree := by
  have hk : 2 ≤ nf.degree := by rcases nf.degree_cases with h | h <;> omega
  have hkpos : 0 < nf.degree := by omega
  have hc : (nf.coefficient : ℂ) ≠ 0 := by exact_mod_cast nf.coefficient_ne_zero
  obtain ⟨c₀, C₀, hc₀, hC₀, hb⟩ := monomial_curve_inverse S a τ hS nf.curve nf.analytic
    nf.coefficient hc nf.degree hk nf.equation φ hnorm hopen hleft hsimple
  let D : ℝ := ‖(nf.coefficient : ℂ)‖ ^ inverseExponent nf.degree
  have hD : 0 < D := Real.rpow_pos_of_pos (norm_pos_iff.mpr hc) _
  refine ⟨c₀*D, C₀*D, mul_pos hc₀ hD, mul_pos hC₀ hD, ?_⟩
  filter_upwards [nf.parameter_limit.eventually hb, nf.physical] with z hzbound hzphysical
  intro hz
  obtain ⟨hm, he, _⟩ := hzphysical
  have hez : (τ : ℂ)+(nf.coefficient : ℂ)*nf.parameter z^nf.degree = z := by
    rw [← he]; ring
  have hi := hzbound (by rwa [hez]) (by rw [← hm]; exact hupper z hz)
    (by rw [hez, ← hm]; exact heq z hz)
  have hscale : ‖z-(τ : ℂ)‖ ^ inverseExponent nf.degree = D*‖nf.parameter z‖^(nf.degree-1) := by
    rw [he]
    exact monomial_norm_power nf.coefficient (nf.parameter z) nf.degree hkpos
  simp only [hez, ← hm] at hi
  rw [hscale]
  have hec : (c₀*D)/(D*‖nf.parameter z‖^(nf.degree-1)) = c₀/‖nf.parameter z‖^(nf.degree-1) := by
    field_simp
  have heC : (C₀*D)/(D*‖nf.parameter z‖^(nf.degree-1)) = C₀/‖nf.parameter z‖^(nf.degree-1) := by
    field_simp
  simpa only [hec, heC] using hi

/-- Actual edge/cusp inverse estimate: the simple kernel, positive opening,
and normalized left functional are derived from the actual regular-frontier
Perron theorem and the already constructed physical normal form. -/
theorem regular_frontier_normal_form_inverse
    (perron : ExternalPerronExistence) {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (nf : PhysicalNormalForm S a τ m (fun j => (Boundary.boundaryVector m (τ : ℂ) j).re)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ z in 𝓝[upper] (τ : ℂ), ∀ hz : 0 < z.im,
      c / ‖z-(τ : ℂ)‖ ^ inverseExponent nf.degree ≤
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ≤
        C / ‖z-(τ : ℂ)‖ ^ inverseExponent nf.degree := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let mB := Boundary.boundaryVector m (τ : ℂ)
  let q : Fin n → ℝ := fun j => ‖mB j‖
  let F := complexMatrixOperator (saturatedMatrix S mB)
  have hreal := Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ
  have hmne := (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  have hq : ∀ j, 0 < q j := fun j => norm_pos_iff.mpr (hmne j)
  have hnfbase : nf.curve 0 = mB := by
    rw [nf.base]
    funext j
    apply Complex.ext <;> simp [mB, hreal j]
  obtain ⟨r, l, hr, hl, hnorm, hright, hleft, hsimple⟩ :=
    regular_frontier_perron_data perron hn algebraic puiseux S a hS hirr m
      hupper heq τ i hfront hτ
  have hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator (fun j => (q j : ℂ)) (Model.action S) h := by
    intro h
    funext j
    simp only [F, complexMatrixOperator_apply, saturatedMatrix,
      DysonPaper.Algebra.scaledOperator, DysonPaper.Algebra.coordMul,
      Model.action_apply, Complex.ofReal_mul, Finset.mul_sum, q]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hsq : ∀ j, (nf.curve 0 j)^2 = (q j : ℂ)^2 := by
    intro j
    rw [hnfbase]
    have he : ((mB j).re : ℂ) = mB j := by
      apply Complex.ext <;> simp [mB, hreal j]
    change (mB j)^2 = (‖mB j‖ : ℂ)^2
    rw [← he, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast (sq_abs (mB j).re).symm
  have hk : 2 ≤ nf.degree := by rcases nf.degree_cases with h | h <;> omega
  have hvker : stabilityCLM S (nf.curve 0) (fun j => (nf.tangent j : ℂ)) = 0 := by
    have hh := monomial_curve_tangent_kernel S a τ nf.curve nf.analytic nf.coefficient
      nf.degree hk nf.equation
    simpa only [nf.derivative.deriv] using hh
  obtain ⟨φ, hφv, hφb, hφleft, hφsimple⟩ := positive_tangent_kernel_data S (nf.curve 0)
    q r l nf.tangent F hq hl nf.tangent_pos hsq hF
    (complexFunctional_left_eigenvector (saturatedMatrix S mB) l hleft) hsimple hvker
  apply physical_normal_form_inverse_of_kernel S a τ m _ hS hupper heq nf φ
  · simpa only [nf.derivative.deriv] using hφv
  · exact hφb
  · exact hφleft
  · simpa only [nf.derivative.deriv] using hφsimple

end NonSymmetricDyson.Full.SingularLinear
