import Dyson.Full.MainLinearExceptional

/-! The exceptional estimates in the original constant-potential variable.
Canonical boundary values are taken for the original family, not assumed to
commute with an independently chosen extension after translation. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.Exceptional
universe u
variable {V : Type u} [Fintype V]

/-- The actual boundary limit at a constant potential becomes the imaginary
origin vector after spectral translation. -/
theorem canonical_constant_origin_data
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j) (a : ℝ) (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => a) z (m z))
    (hregular : a ∉ Boundary.singularUnion m)
    (hbulk : BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (a : ℂ))) :
    let q : V → ℝ := fun i => (Boundary.boundaryVector m (a : ℂ) i).im
    (∀ i, 0 < q i) ∧
    Boundary.boundaryVector m (a : ℂ) = BulkOriginData.imaginaryVector q ∧
    BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q) ∧
    Tendsto (fun w : ℂ => m (w + (a : ℂ))) (𝓝[ExternalAlgebraic.upper] 0)
      (𝓝 (BulkOriginData.imaginaryVector q)) ∧
    Tendsto (fun w : ℂ => Boundary.boundaryVector m (w + (a : ℂ)))
      (𝓝[ExternalAlgebraic.upper] 0) (𝓝 (BulkOriginData.imaginaryVector q)) := by
  dsimp only
  have hvert := Boundary.family_boundary_limits algebraic puiseux S (fun _ => a) hS m hupper heq a hregular
  have hshift (z : ℂ) (hz : 0 < z.im) : BasicEstimates.IsDysonSolution S (fun _ => 0) z
      (m (z + (a : ℂ))) := by
    have hh := (SpectralShift.constant_dyson_shift S a (z + (a : ℂ)) (m (z + (a : ℂ)))).mp
      (heq _ (by simpa using hz))
    simpa using hh
  have him := Origin.imaginary_boundary_of_limit S (fun η : ℝ => m ((η : ℂ) * Complex.I + (a : ℂ)))
    (Boundary.boundaryVector m (a : ℂ)) hS
    (fun η hη => hupper _ (by simpa using hη))
    (fun η hη => hshift _ (by simpa using hη))
    (by simpa [Boundary.IsBoundaryValue, add_comm] using hvert)
  have ht : Tendsto (fun w : ℂ => w + (a : ℂ)) (𝓝[ExternalAlgebraic.upper] 0)
      (𝓝[ExternalAlgebraic.upper] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun w : ℂ => w + (a : ℂ)) (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ) + (a : ℂ))) :=
        (continuous_id.add continuous_const).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hcont := Boundary.family_boundary_continuous algebraic puiseux S (fun _ => a) hS m hupper heq
    (a : ℂ) (Or.inr ⟨a, hregular, rfl⟩)
  have hlimM := (hcont.mono (show ExternalAlgebraic.upper ⊆ Boundary.commonRegularDomain m
    from fun _ hz => Or.inl hz)).tendsto.comp ht
  have hlim : Tendsto (fun w : ℂ => m (w + (a : ℂ))) (𝓝[ExternalAlgebraic.upper] 0)
      (𝓝 (Boundary.boundaryVector m (a : ℂ))) := by
    apply hlimM.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Boundary.family_extension_agrees S (fun _ => a) hS m hupper heq _ (by simpa using hz)
  refine ⟨hbulk, him, ?_, ?_, ?_⟩
  · rw [← him]
    have hb := (Boundary.family_boundary_equation algebraic puiseux S (fun _ => a) hS m
      hupper heq a hregular).2.2
    simpa using (SpectralShift.constant_dyson_shift S a (a : ℂ) _).mp hb
  · rw [← him]
    exact hlim
  · rw [← him]
    exact hlimM

/-- Glue a canonical extension to the actual upper-half-plane family.
The origin data are needed only when the compact energy set contains zero. -/
theorem exceptional_strip_of_extension [Nonempty V]
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (m M : ℂ → V → ℂ)
    (hupper : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (m z))
    (hagree : ∀ z : ℂ, 0 < z.im → M z = m z)
    (J : Set ℝ) (hJ : IsCompact J)
    (hcont : ContinuousOn M (MainLinearBulk.closedStrip J))
    (hu : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsUpperSolution (M z))
    (he : ∀ z ∈ MainLinearBulk.closedStrip J, BasicEstimates.IsDysonSolution S (fun _ => 0) z (M z))
    (hboundary : ∀ E ∈ J, E ≠ 0 → Function.Bijective (InteriorStability.stabilityOperator S (M (E : ℂ))))
    (horigin : (0 : ℝ) ∈ J → ∃ q : V → ℝ, (∀ i, 0 < q i) ∧
      BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q) ∧
      Tendsto M (𝓝[ExternalAlgebraic.upper] 0) (𝓝 (BulkOriginData.imaginaryVector q)))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z‖⁻¹ := by
  classical
  have huAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsUpperSolution (M z) := by
    intro z hz
    rw [hagree z hz]
    exact hupper z hz
  have heAll : ∀ z : ℂ, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => 0) z (M z) := by
    intro z hz
    rw [hagree z hz]
    exact heq z hz
  by_cases hzero : (0 : ℝ) ∈ J
  · obtain ⟨q, hq, hsol₀, hlim⟩ := horigin hzero
    obtain ⟨c, C, hc', hC, hb⟩ := MainLinearBulk.origin_full_strip_from_model J hJ S
      M hS hcont hu he hboundary external q hc hq hsol₀ t ht hs huAll heAll hlim
    refine ⟨c, C, hc', hC, ?_⟩
    intro z hzJ hz
    simpa only [hagree z hz] using hb z hzJ hz
  · have hbij : ∀ E ∈ J, Function.Bijective (InteriorStability.stabilityOperator S (M (E : ℂ))) := by
      intro E hE
      exact hboundary E hE (by intro he0; exact hzero (he0 ▸ hE))
    obtain ⟨c, C, hc', hC, hb⟩ := MainLinearBulk.full_strip_inverse_bounds J hJ S (fun _ => 0)
      M hS hcont hu he hbij
    let N : ℂ → ℝ := fun z => if hz : 0 < z.im then
      ‖EuclideanInverse.stabilityInverse S (fun _ => 0) z (m z) hS hz (hupper z hz) (heq z hz)‖ else 0
    have hN : ∀ z : ℂ, z.re ∈ J → 0 < z.im → c ≤ N z ∧ N z ≤ C := by
      intro z hzJ hz
      simpa only [N, dif_pos hz, hagree z hz] using hb z hzJ hz
    obtain ⟨c', C', hc'', hC', hh⟩ := weighted_bound_of_zero_not_mem J hJ hzero N c C hc' hC hN
    refine ⟨c', C', hc'', hC', ?_⟩
    intro z hzJ hz
    simpa only [N, dif_pos hz] using hh z hzJ hz

/-- Constant-potential closure in the original spectral variable. -/
theorem canonical_constant_exceptional_strip [Nonempty V]
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (external : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hc : Resonance.StronglyConnected (fun i j => 0 < S i j))
    (a : ℝ) (m : ℂ → V → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S (fun _ => a) z (m z))
    (J : Set ℝ) (hJ : IsCompact J)
    (hregular : ∀ E ∈ J, E ∉ Boundary.singularUnion m)
    (hbulk : ∀ E ∈ J, BasicEstimates.IsUpperSolution (Boundary.boundaryVector m (E : ℂ)))
    (hboundary : ∀ E ∈ J, E ≠ a → Function.Bijective
      (InteriorStability.stabilityOperator S (Boundary.boundaryVector m (E : ℂ))))
    (t : V → ℂ) (ht : ∀ i, t i ^ 2 = 1)
    (hs : ∀ i j, S i j ≠ 0 → t j = -t i) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, z.re ∈ J → ∀ hz : 0 < z.im,
      c * max 1 ‖z - (a : ℂ)‖⁻¹ ≤ ‖EuclideanInverse.stabilityInverse S (fun _ => a) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S (fun _ => a) z (m z) hS hz
        (hupper z hz) (heq z hz)‖ ≤ C * max 1 ‖z - (a : ℂ)‖⁻¹ := by
  let J' := SpectralShift.shiftedInterval J a
  let n : ℂ → V → ℂ := fun w => m (w + (a : ℂ))
  let M : ℂ → V → ℂ := fun w => Boundary.boundaryVector m (w + (a : ℂ))
  have hnupper : ∀ w : ℂ, 0 < w.im → BasicEstimates.IsUpperSolution (n w) := by
    intro w hw
    exact hupper _ (by simpa using hw)
  have hneq : ∀ w : ℂ, 0 < w.im → BasicEstimates.IsDysonSolution S (fun _ => 0) w (n w) := by
    intro w hw
    simpa [n] using (SpectralShift.constant_dyson_shift S a (w + (a : ℂ)) _).mp
      (heq _ (by simpa using hw))
  obtain ⟨hcont, hu, he⟩ := canonical_closed_strip_data algebraic puiseux S (fun _ => a) hS m hupper heq
    J hregular hbulk
  have hmap : ∀ w ∈ MainLinearBulk.closedStrip J', w + (a : ℂ) ∈ MainLinearBulk.closedStrip J := by
    intro w hw
    constructor
    · have hh : w.re + a ∈ J := (SpectralShift.shiftedInterval_mem J a (w.re + a)).mp (by simpa using hw.1)
      simpa using hh
    · simpa using hw.2
  have hcont' : ContinuousOn M (MainLinearBulk.closedStrip J') :=
    hcont.comp (continuous_id.add continuous_const).continuousOn hmap
  have hu' : ∀ w ∈ MainLinearBulk.closedStrip J', BasicEstimates.IsUpperSolution (M w) :=
    fun w hw => hu _ (hmap w hw)
  have he' : ∀ w ∈ MainLinearBulk.closedStrip J', BasicEstimates.IsDysonSolution S (fun _ => 0) w (M w) := by
    intro w hw
    simpa [M] using (SpectralShift.constant_dyson_shift S a (w + (a : ℂ)) _).mp (he _ (hmap w hw))
  have hagree : ∀ w : ℂ, 0 < w.im → M w = n w := by
    intro w hw
    exact Boundary.family_extension_agrees S (fun _ => a) hS m hupper heq _ (by simpa using hw)
  have hbd' : ∀ E ∈ J', E ≠ 0 → Function.Bijective (InteriorStability.stabilityOperator S (M (E : ℂ))) := by
    intro E hE hEn
    have hh : E + a ∈ J := (SpectralShift.shiftedInterval_mem J a (E + a)).mp (by simpa using hE)
    simpa [M] using hboundary (E + a) hh (by intro h; exact hEn (by linarith))
  have horigin : (0 : ℝ) ∈ J' → ∃ q : V → ℝ, (∀ i, 0 < q i) ∧
      BasicEstimates.IsDysonSolution S (fun _ => 0) 0 (BulkOriginData.imaginaryVector q) ∧
      Tendsto M (𝓝[ExternalAlgebraic.upper] 0) (𝓝 (BulkOriginData.imaginaryVector q)) := by
    intro h0
    have haJ : a ∈ J := (SpectralShift.shiftedInterval_mem J a a).mp (by simpa using h0)
    obtain ⟨hq, _, hsol₀, _, hlim⟩ := canonical_constant_origin_data algebraic puiseux S hS a m
      hupper heq (hregular a haJ) (hbulk a haJ)
    exact ⟨_, hq, hsol₀, hlim⟩
  obtain ⟨c, C, hc', hC, hb⟩ := exceptional_strip_of_extension external S hS hc n M hnupper hneq hagree
    J' (SpectralShift.shiftedInterval_compact J hJ a) hcont' hu' he' hbd' horigin t ht hs
  refine ⟨c, C, hc', hC, ?_⟩
  intro z hzJ hz
  have hz' : 0 < (z - (a : ℂ)).im := by simpa using hz
  have hj' : (z - (a : ℂ)).re ∈ J' := by
    exact (SpectralShift.shiftedInterval_mem J a z.re).mpr hzJ
  have hh := hb (z - (a : ℂ)) hj' hz'
  have hinv := SpectralShift.inverse_independent_of_presentation S (fun _ => a) (fun _ => 0)
    z (z - (a : ℂ)) (m z) hS hz hz' (hupper z hz) (heq z hz)
    ((SpectralShift.constant_dyson_shift S a z (m z)).mp (heq z hz))
  simpa only [n, sub_add_cancel, ← hinv] using hh

end NonSymmetricDyson.Full.Exceptional
