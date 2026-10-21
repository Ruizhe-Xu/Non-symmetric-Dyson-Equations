import Dyson.Full.PoissonDensity
import Dyson.Full.MainDecomposition

/-! M6's corrected Poisson argument.  Remote positive mass is retained,
including every atom.  The three integral estimates have already been proved
from actual measure integrals in Full.PoissonDensity. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NonSymmetricDyson.Paper.LinearPoisson
open Full.Poisson

/-- The precise finite-atomic term written in the revised manuscript is
nonnegative and O(η), uniformly as the energy stays near the regular point. -/
theorem finite_atomic_tail (A : Finset ℝ) (Δ : ℝ → ℝ)
    {τ E η r : ℝ} (hr : 0<r) (hη : 0≤η) (hE : |E-τ|≤r/2)
    (hΔ : ∀ t∈A,0≤Δ t) (hsep : ∀ t∈A,r≤|t-τ|) :
    0≤∑ t∈A, Δ t*kernel E η t ∧
    (∑ t∈A, Δ t*kernel E η t)≤(4/r^2)*(∑ t∈A,Δ t)*η := by
  constructor
  · exact Finset.sum_nonneg fun t ht => mul_nonneg (hΔ t ht) (kernel_nonneg hη)
  · calc
      _ ≤ ∑ t∈A, Δ t*(4*η/r^2) := Finset.sum_le_sum fun t ht =>
        mul_le_mul_of_nonneg_left (remote_kernel_bound hr hη hE (hsep t ht)) (hΔ t ht)
      _ = _ := by rw [← Finset.sum_mul]; ring

/-- The exact density-plus-remote decomposition; the remainder integrates
the entire remote spectral measure, so atoms need no absolute-continuity
assumption and cannot silently disappear. -/
theorem poisson_local_with_all_atoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ E η r : ℝ} (hr : 0<r) (hη : 0<η) (hE : |E-τ|≤r/2) :
    ∃ error : ℝ, 0≤error ∧ error≤4*η/r^2 ∧
      (stieltjes μ (point E η)).im =
        (∫ t in {t : ℝ | |t-τ|<r},kernel E η t ∂μ)+error :=
  local_remote_representation μ hr hη hE

/-- Actual edge support-side integral estimate, including the atomic tail. -/
theorem edge_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {c C r κ η : ℝ}
    (hc : 0≤c) (hC : 0≤C) (hr : 0<r) (hκ : 0≤κ) (hη : 0<η)
    (hsmall : κ+η<r/8) (hq : κ+η≤1)
    (hv : Measurable v) (hn : ∀x,0≤v x)
    (hl : ∀x∈Ioo 0 r,c*|x|^((1:ℝ)/2)≤v x)
    (hu : ∀x∈Ioo 0 r,v x≤C*|x|^((1:ℝ)/2))
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/5)*(κ+η)^((1:ℝ)/2)≤(stieltjes μ (point κ η)).im ∧
    (stieltjes μ (point κ η)).im≤
      (C*(Real.pi+fractionalMoment ((1:ℝ)/2))+4/r^2)*(κ+η)^((1:ℝ)/2) :=
  edge_support_measure_scale μ (by norm_num) (by norm_num) hc hC hr hκ hη hsmall hq hv hn hl hu hμ

theorem edge_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {c C r κ η : ℝ}
    (hc : 0≤c) (hC : 0≤C) (hr : 0<r) (hκ : 0≤κ) (hη : 0<η)
    (hsmall : κ+η<r/8) (hq : κ+η≤1)
    (hv : Measurable v) (hn : ∀x,0≤v x)
    (hl : ∀x∈Ioo 0 r,c*|x|^((1:ℝ)/2)≤v x)
    (hu : ∀x∈Ioo 0 r,v x≤C*|x|^((1:ℝ)/2))
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo 0 r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/10)*(η/Real.sqrt (κ+η))≤(stieltjes μ (point (-κ) η)).im ∧
    (stieltjes μ (point (-κ) η)).im≤
      (2*C*gapMoment ((1:ℝ)/2)+4/r^2)*(η/Real.sqrt (κ+η)) := by
  simpa only [half_gap_scale] using edge_gap_measure_scale μ (by norm_num : (0:ℝ)<1/2)
    (by norm_num) hc hC hr hκ hη hsmall hq hv hn hl hu hμ

theorem cusp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {c C r E η : ℝ}
    (hc : 0≤c) (hC : 0≤C) (hr : 0<r) (hη : 0<η)
    (hsmall : |E|+η<r/8) (hq : |E|+η≤1)
    (hv : Measurable v) (hn : ∀x,0≤v x)
    (hl : ∀x∈Ioo (-r) r,c*|x|^((1:ℝ)/3)≤v x)
    (hu : ∀x∈Ioo (-r) r,v x≤C*|x|^((1:ℝ)/3))
    (hμ : μ.restrict (Ioo (-r) r) =
      (volume.restrict (Ioo (-r) r)).withDensity (fun x => ENNReal.ofReal (v x))) :
    (c/5)*(|E|+η)^((1:ℝ)/3)≤(stieltjes μ (point E η)).im ∧
    (stieltjes μ (point E η)).im≤
      (C*(Real.pi+fractionalMoment ((1:ℝ)/3))+4/r^2)*(|E|+η)^((1:ℝ)/3) :=
  cusp_measure_scale μ (by norm_num) (by norm_num) hc hC hr hη hsmall hq hv hn hl hu hμ

end NonSymmetricDyson.Paper.LinearPoisson
