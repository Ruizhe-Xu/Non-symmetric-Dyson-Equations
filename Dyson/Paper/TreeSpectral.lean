import Mathlib

/-! Explicit standard external spectral theory for an arbitrary bounded
self-adjoint operator on a complete complex Hilbert space. Every inverse,
inner product and measure in the interface is an actual mathematical object.
No finite type matrix, tree, or Dyson equation occurs in this interface. -/
noncomputable section
open scoped Topology InnerProductSpace
open MeasureTheory
namespace NonSymmetricDyson.Paper.TreeSpectral
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ordinary bounded self-adjoint resolvent and vector spectral measure
facts, in the sign convention `(J−zI)⁻¹`. The probability normalization is
asserted only for unit vectors. -/
structure ResolventMeasureData (J : H →L[ℂ] H) where
  green : ℂ → H →L[ℂ] H
  shifted : ∀ z : ℂ, 0 < z.im → H ≃L[ℂ] H
  shifted_apply : ∀ (z : ℂ) (hz : 0 < z.im) (x : H),
    shifted z hz x = J x-z • x
  green_eq : ∀ (z : ℂ) (hz : 0 < z.im),
    green z = (shifted z hz).symm.toContinuousLinearMap
  scalar_analytic : ∀ u : H,
    AnalyticOnNhd ℂ (fun z => inner ℂ u (green z u)) {z : ℂ | 0 < z.im}
  norm_green : ∀ (z : ℂ), 0 < z.im → ‖green z‖ ≤ z.im⁻¹
  imaginary_identity : ∀ (z : ℂ), 0 < z.im → ∀ u : H,
    (inner ℂ u (green z u)).im = z.im * ‖green z u‖^2
  spectral_measure : ∀ u : H, ‖u‖ = 1 →
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-‖J‖) ‖J‖)ᶜ = 0 ∧
      ∀ z : ℂ, 0 < z.im →
        inner ℂ u (green z u) = ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂μ

/-- General external bounded self-adjoint spectral theorem and resolvent
facts. Its quantifiers range over arbitrary complete complex Hilbert spaces
and arbitrary self-adjoint bounded operators. -/
def BoundedSelfAdjointSpectralPrinciple : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ J : H →L[ℂ] H, IsSelfAdjoint J → Nonempty (ResolventMeasureData J)

namespace ResolventMeasureData
variable {J : H →L[ℂ] H} (data : ResolventMeasureData J)

/-- The selected Green operator is a genuine right inverse. -/
theorem green_right_inverse (z : ℂ) (hz : 0 < z.im) (u : H) :
    J (data.green z u)-z • data.green z u = u := by
  rw [←data.shifted_apply z hz,data.green_eq z hz]
  exact (data.shifted z hz).apply_symm_apply u

/-- The selected Green operator is a genuine left inverse. -/
theorem green_left_inverse (z : ℂ) (hz : 0 < z.im) (u : H) :
    data.green z (J u-z • u) = u := by
  rw [←data.shifted_apply z hz,data.green_eq z hz]
  exact (data.shifted z hz).symm_apply_apply u

theorem green_ne_zero (z : ℂ) (hz : 0 < z.im) {u : H} (hu : u ≠ 0) :
    data.green z u ≠ 0 := by
  intro hg
  have h := data.green_right_inverse z hz u
  rw [hg,map_zero,smul_zero,sub_zero] at h
  exact hu h.symm

/-- Strict positivity follows from the exact resolvent imaginary identity
and injectivity; it is not a Dyson or tree positivity assumption. -/
theorem scalar_im_pos (z : ℂ) (hz : 0 < z.im) {u : H} (hu : u ≠ 0) :
    0 < (inner ℂ u (data.green z u)).im := by
  rw [data.imaginary_identity z hz]
  exact mul_pos hz (sq_pos_of_pos (norm_pos_iff.mpr (data.green_ne_zero z hz hu)))

/-- Cauchy–Schwarz and the operator resolvent bound imply the scalar bound. -/
theorem scalar_norm_le (z : ℂ) (hz : 0 < z.im) (u : H) :
    ‖inner ℂ u (data.green z u)‖ ≤ ‖u‖^2*z.im⁻¹ := by
  calc
    _ ≤ ‖u‖*‖data.green z u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖*(‖data.green z‖*‖u‖) :=
      mul_le_mul_of_nonneg_left ((data.green z).le_opNorm u) (norm_nonneg _)
    _ ≤ ‖u‖*(z.im⁻¹*‖u‖) := by gcongr; exact data.norm_green z hz
    _ = _ := by ring

theorem unit_scalar_norm_le (z : ℂ) (hz : 0 < z.im) (u : H) (hu : ‖u‖ = 1) :
    ‖inner ℂ u (data.green z u)‖ ≤ z.im⁻¹ := by
  simpa [hu] using data.scalar_norm_le z hz u

/-- A verified norm estimate enlarges the spectral support interval. -/
theorem spectral_measure_of_norm_bound (u : H) (hu : ‖u‖ = 1)
    (C : ℝ) (hC : ‖J‖ ≤ C) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-C) C)ᶜ = 0 ∧
      ∀ z : ℂ, 0 < z.im →
        inner ℂ u (data.green z u) = ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂μ := by
  obtain ⟨μ,hμ,hs,hr⟩ := data.spectral_measure u hu
  refine ⟨μ,hμ,?_,hr⟩
  apply measure_mono_null _ hs
  exact Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (neg_le_neg hC) hC)

end ResolventMeasureData

/-- Ordinary uniqueness of the scalar Stieltjes transform of probability
measures. This separate universal input avoids importing an existence or
Dyson-specific representation hypothesis into the tree construction. -/
def ScalarStieltjesUniqueness : Prop :=
  ∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    (∀ z : ℂ, 0 < z.im →
      (∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂μ) = ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂ν) → μ = ν

theorem measure_unique (external : ScalarStieltjesUniqueness)
    (f : ℂ → ℂ) (μ ν : Measure ℝ) (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν)
    (hrepμ : ∀ z : ℂ, 0 < z.im → f z = ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂μ)
    (hrepν : ∀ z : ℂ, 0 < z.im → f z = ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂ν) : μ = ν := by
  apply external μ ν hμ hν
  intro z hz
  exact (hrepμ z hz).symm.trans (hrepν z hz)

end NonSymmetricDyson.Paper.TreeSpectral
