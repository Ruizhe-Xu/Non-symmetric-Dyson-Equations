import Dyson.Full.SingularDensityInverse
import Dyson.Full.PerronDensityComparison
import Dyson.Full.MainSingularities

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.SingularLinear
open Singularities SingularSpectral Spectral ExternalAlgebraic
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Exact diagonal conjugation transfers the actual Dyson stability inverse
bound to the reduced operator, with explicit uniform constants. -/
theorem reduced_inverse_norm_transfer
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
    (hS : ∀ i j,0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (q Q : ℝ) (hq : 0<q) (hQ : 0<Q) (hlo : ∀ i,q≤‖m i‖) (hhi : ∀ i,‖m i‖≤Q)
    (d : SimpleSpectralSplit (reducedOperator S m)) :
    ‖EuclideanInverse.conjugate d.inverse‖≤
      (Real.sqrt (Fintype.card ι))^2*(Q/q)*
        ‖EuclideanInverse.stabilityInverse S a z m hS hz hm heq‖ := by
  let e := InteriorStability.stabilityContinuousEquiv hS hz hm heq
  let B : ℝ := Real.sqrt (Fintype.card ι)*‖EuclideanInverse.stabilityInverse S a z m hS hz hm heq‖
  have hB : 0≤B := by dsimp [B]; positivity
  have heB : ‖e.symm.toContinuousLinearMap‖≤B := EuclideanInverse.conjugate_norm_lower _
  have hcoerce (v : ι → ℂ) : ‖v‖≤B*‖InteriorStability.stabilityOperator S m v‖ := by
    have hh := e.symm.toContinuousLinearMap.le_opNorm (e v)
    have hi : e.symm.toContinuousLinearMap (e v)=v := e.symm_apply_apply v
    rw [hi] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right heB (norm_nonneg _))
  have hβ := spectral_value_ne_zero_upper S a z m hS hz hm heq d
  have hnorm : ‖d.inverse‖≤B*Q/q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    let x := d.inverse y
    let v : ι → ℂ := fun i => (‖m i‖:ℂ)*x i
    have hx : reducedOperator S m x=y := d.inverse_right hβ y
    have hLv : InteriorStability.stabilityOperator S m v=
        fun i => ((m i)^2/(‖m i‖:ℂ))*y i := by
      funext i
      rw [reduced_stability_identity S m (fun j => BasicEstimates.component_ne_zero hm j) x i,hx]
    have hb : ‖InteriorStability.stabilityOperator S m v‖≤Q*‖y‖ := by
      rw [hLv]
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      have hmi : ‖m i‖≠0 := norm_ne_zero_iff.mpr (BasicEstimates.component_ne_zero hm i)
      have hc : ‖(m i)^2/(‖m i‖:ℂ)‖=‖m i‖ := by
        simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_norm]
        field_simp
      rw [norm_mul,hc]
      exact mul_le_mul (hhi i) (norm_le_pi_norm y i) (norm_nonneg _) hQ.le
    have hv : ‖v‖≤B*Q*‖y‖ := (hcoerce v).trans
      ((mul_le_mul_of_nonneg_left hb hB).trans_eq (by ring))
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hvi : q*‖x i‖≤‖v‖ := by
      calc
        _ ≤ ‖m i‖*‖x i‖ := mul_le_mul_of_nonneg_right (hlo i) (norm_nonneg _)
        _ = ‖v i‖ := by dsimp [v]; simp
        _ ≤ ‖v‖ := norm_le_pi_norm v i
    have hh := hvi.trans hv
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    convert hh using 1 <;> ring
  exact (EuclideanInverse.conjugate_norm_upper d.inverse).trans
    ((mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)).trans_eq (by dsimp [B]; ring))

/-- The original local reduced inverse bound ‖R⁻¹‖≲ρ⁻², for the actual
physical solution near either an edge or a cusp. Here ρ is the manuscript's sum of
component imaginary parts. -/
theorem regular_frontier_reduced_density_inverse
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
      ∀ d : SimpleSpectralSplit (reducedOperator S (m z)),
        ‖EuclideanInverse.conjugate d.inverse‖≤C/(∑ j,(m z j).im)^2 := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨C,hC,hbound⟩ := regular_frontier_density_inverse perron hn algebraic puiseux
    S a hS hirr m hupper heq τ i hfront hτ nf
  have hm : Tendsto m (𝓝[upper] (τ:ℂ)) (𝓝 (Boundary.boundaryVector m (τ:ℂ))) := by
    have hc := (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq)
      (τ:ℂ) (Or.inr ⟨τ,hτ,rfl⟩)
    have ht := (hc.mono (show upper⊆Boundary.commonRegularDomain m from fun _ hz => Or.inl hz)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S a hS m hupper heq z hz
  obtain ⟨q,hq,hqlow⟩ := PerronContinuation.positive_component_lower_bound m _ hm
    (Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ).1
  let Q : ℝ := ‖Boundary.boundaryVector m (τ:ℂ)‖+1
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hqhi : ∀ᶠ z in 𝓝[upper] (τ:ℂ),‖m z‖≤Q := hm.norm.eventually_le_const (by dsimp [Q]; linarith)
  let A : ℝ := (Real.sqrt (Fintype.card (Fin n)))^2*(Q/q)
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨A*C,mul_pos hA hC,?_⟩
  filter_upwards [hbound,hqlow,hqhi] with z hzbound hzlow hzhi
  intro hz d
  have ht := reduced_inverse_norm_transfer S a z (m z) hS hz (hupper z hz) (heq z hz)
    q Q hq hQ hzlow (fun j => (norm_le_pi_norm (m z) j).trans hzhi) d
  have hρ : 0<∑ j,(m z j).im := Finset.sum_pos (fun j _ => hupper z hz j) Finset.univ_nonempty
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  have hh := mul_le_mul_of_nonneg_right ht (sq_nonneg (∑ j,(m z j).im))
  exact hh.trans (by simpa [A,mul_assoc] using mul_le_mul_of_nonneg_left (hzbound hz) hA.le)

/-- The physical normal form is constructed from the actual model hypotheses. -/
theorem actual_regular_frontier_reduced_density_inverse
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple) {n : ℕ} (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀ hz:0<z.im,
      ∀ d : SimpleSpectralSplit (reducedOperator S (m z)),
        ‖EuclideanInverse.conjugate d.inverse‖≤C/(∑ j,(m z j).im)^2 := by
  obtain ⟨nf⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  exact regular_frontier_reduced_density_inverse perron hn algebraic puiseux
    S a hS hirr m hupper heq τ i hfront hτ nf

end NonSymmetricDyson.Full.SingularLinear
