import Mathlib
import Dyson.GlobalWellPosedness
import Dyson.HighEnergy
import Dyson.ComponentBounds

/-!
# The complete first main theorem relative to external Stieltjes theory

The only imported mathematical arguments are stated in `ExternalStieltjesTheory`.
They concern arbitrary holomorphic Herglotz functions and arbitrary probability
measures, not Dyson equations. In particular compact support is NOT a field of
a Dyson-solution interface: the exterior estimate is established below from
the equation, continuity, and the large-height bound.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace NonSymmetricDyson.Full.Foundations

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def Represents (f : ℂ → ℂ) (μ : Measure ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im → f z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ

def NormalizedAtInfinity (f : ℂ → ℂ) : Prop :=
  ∀ zs : ℕ → ℂ, (∀ n, 0 < (zs n).im) →
    Tendsto (fun n => (zs n).im) atTop atTop →
      Tendsto (fun n => zs n * f (zs n)) atTop (𝓝 (-1 : ℂ))

/-- General external complex-analysis and measure-theory arguments.

`representation` is the normalized Herglotz representation theorem, written
coordinatewise for a finite holomorphic family. `uniqueness` is Stieltjes
uniqueness. `support_of_poisson_decay` is the standard support consequence of
Stieltjes inversion: pointwise linear Poisson decay on an open set rules out
measure on that set. None of these statements mentions `S`, `a`, or Dyson.
-/
structure ExternalStieltjesTheory (ι : Type*) [Fintype ι] : Prop where
  representation : ∀ m : ℂ → ι → ℂ,
    AnalyticOnNhd ℂ m {z : ℂ | 0 < z.im} →
    (∀ z, 0 < z.im → ∀ i, 0 < (m z i).im) →
    (∀ i, NormalizedAtInfinity (fun z => m z i)) →
    ∃ μ : ι → Measure ℝ, ∀ i, IsProbabilityMeasure (μ i) ∧
      Represents (fun z => m z i) (μ i)
  uniqueness : ∀ (f : ℂ → ℂ) (μ ν : Measure ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Represents f μ → Represents f ν → μ = ν
  support_of_poisson_decay : ∀ (f : ℂ → ℂ) (μ : Measure ℝ) (b : ℝ),
    IsProbabilityMeasure μ → Represents f μ → 0 ≤ b →
    (∀ E : ℝ, b < |E| → ∃ C : ℝ, 0 ≤ C ∧
      ∀ η : ℝ, 0 < η → (f ((E : ℂ) + (η : ℂ) * Complex.I)).im ≤ C * η) →
    μ (Set.Icc (-b) b)ᶜ = 0

/-- Supremum norm is attained in finite nonempty dimension. -/
theorem exists_norm_eq (x : ι → ℂ) : ∃ i, ‖x i‖ = ‖x‖ := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖)
    Finset.univ_nonempty
  refine ⟨i, le_antisymm (norm_le_pi_norm x i) ?_⟩
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun j => hi j (Finset.mem_univ j))

theorem action_norm_bound {S : ι → ι → ℝ} (hS : ∀ i j, 0 ≤ S i j)
    (m : ι → ℂ) (i : ι) :
    ‖∑ j, (S i j : ℂ) * m j‖ ≤ (∑ j, S i j) * ‖m‖ := by
  calc
    _ ≤ ∑ j, ‖(S i j : ℂ) * m j‖ := norm_sum_le _ _
    _ = ∑ j, S i j * ‖m j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [norm_mul, abs_of_nonneg (hS i j)]
    _ ≤ ∑ j, S i j * ‖m‖ := Finset.sum_le_sum
      (fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm m j) (hS i j))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The scalar inequality driving the exterior barrier. -/
theorem energy_norm_bound {S : ι → ι → ℝ} {a : ι → ℝ}
    {z : ℂ} {m : ι → ℂ} (hS : ∀ i j, 0 ≤ S i j)
    (hsol : BasicEstimates.IsDysonSolution S a z m) (i : ι) :
    |z.re| ≤ |a i| + ‖m i‖⁻¹ + (∑ j, S i j) * ‖m‖ := by
  have heq : z - (a i : ℂ) = -(m i)⁻¹ - ∑ j, (S i j : ℂ) * m j := by
    linear_combination -(hsol i)
  have hn : ‖z - (a i : ℂ)‖ ≤ ‖m i‖⁻¹ + (∑ j, S i j) * ‖m‖ := by
    rw [heq]
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (action_norm_bound hS m i) ‖-(m i)⁻¹‖)
  have hre : |z.re - a i| ≤ ‖z - (a i : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (a i : ℂ))
  have htri : |z.re| ≤ |z.re - a i| + |a i| := by
    simpa using abs_add_le (z.re - a i) (a i)
  linarith

/-- There is no crossing of the critical modulus outside the support radius. -/
theorem norm_ne_barrier {S : ι → ι → ℝ} {a : ι → ℝ}
    {z : ℂ} {m : ι → ℂ} {A r : ℝ}
    (hS : ∀ i j, 0 ≤ S i j) (ha : ∀ i, |a i| ≤ A)
    (hr : 0 < r) (hrow : ∀ i, ∑ j, S i j ≤ r ^ 2)
    (hE : A + 2 * r < |z.re|)
    (hsol : BasicEstimates.IsDysonSolution S a z m) : ‖m‖ ≠ r⁻¹ := by
  intro heq
  obtain ⟨i, hi⟩ := exists_norm_eq m
  have h := energy_norm_bound hS hsol i
  rw [hi, heq, inv_inv] at h
  have hrow' : (∑ j, S i j) * r⁻¹ ≤ r := by
    calc
      _ ≤ r ^ 2 * r⁻¹ := mul_le_mul_of_nonneg_right (hrow i) (inv_nonneg.mpr hr.le)
      _ = r := by field_simp [hr.ne']
  linarith [ha i]

/-- A continuous scalar function cannot cross a forbidden level on a positive
half-line. The seed may be chosen at a larger height depending on the point. -/
theorem below_barrier_of_continuous {f : ℝ → ℝ} {b : ℝ}
    (hf : ContinuousOn f (Set.Ioi 0))
    (hne : ∀ t, 0 < t → f t ≠ b)
    (hseed : ∀ t, 0 < t → ∃ H, t ≤ H ∧ f H < b) :
    ∀ t, 0 < t → f t < b := by
  intro t ht
  by_contra h
  have hb : b ≤ f t := le_of_not_gt h
  obtain ⟨H, htH, hH⟩ := hseed t ht
  have hc : ContinuousOn f (Set.Icc t H) := hf.mono
    (fun x hx => lt_of_lt_of_le ht hx.1)
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc' htH hc ⟨hH.le, hb⟩
  exact hne u (lt_of_lt_of_le ht hu.1) hue

def vertical (E η : ℝ) : ℂ := (E : ℂ) + (η : ℂ) * Complex.I

@[simp] theorem vertical_re (E η : ℝ) : (vertical E η).re = E := by
  simp [vertical]
@[simp] theorem vertical_im (E η : ℝ) : (vertical E η).im = η := by
  simp [vertical]

theorem vertical_continuous (E : ℝ) : Continuous (vertical E) := by
  unfold vertical
  fun_prop

theorem canonical_norm_lt_barrier {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {A r E : ℝ}
    (ha : ∀ i, |a i| ≤ A) (hr : 0 < r)
    (hrow : ∀ i, ∑ j, S i j ≤ r ^ 2) (hE : A + 2 * r < |E|)
    {η : ℝ} (hη : 0 < η) :
    ‖GlobalWellPosedness.solution S a hS (vertical E η)‖ < r⁻¹ := by
  let m := GlobalWellPosedness.solution S a hS
  have hf : ContinuousOn (fun t : ℝ => ‖m (vertical E t)‖) (Set.Ioi 0) := by
    apply ContinuousOn.norm
    exact (GlobalWellPosedness.solution_continuousOn a hS).comp
      (vertical_continuous E).continuousOn (by intro t ht; simpa using ht)
  apply below_barrier_of_continuous hf ?_ ?_ η hη
  · intro t ht
    exact norm_ne_barrier hS ha hr hrow (by simpa using hE)
      (GlobalWellPosedness.solution_equation a hS (by simpa using ht))
  · intro t ht
    let H : ℝ := t + r + 1
    have hH : 0 < H := by dsimp [H]; linarith
    have hrH : r < H := by dsimp [H]; linarith
    refine ⟨H, by dsimp [H]; linarith, ?_⟩
    have hn : ‖m (vertical E H)‖ ≤ H⁻¹ := by
      apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hH.le)).mpr
      intro i
      simpa [m] using GlobalWellPosedness.solution_norm_le a hS
        (z := vertical E H) (by simpa using hH) i
    exact hn.trans_lt (inv_strictAnti₀ hr hrH)

/-- Improved exterior modulus bound, with a strict contraction margin. -/
theorem canonical_exterior_norm_bound {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {A r E : ℝ}
    (ha : ∀ i, |a i| ≤ A) (hr : 0 < r)
    (hrow : ∀ i, ∑ j, S i j ≤ r ^ 2) (hE : A + 2 * r < |E|)
    {η : ℝ} (hη : 0 < η) (i : ι) :
    ‖GlobalWellPosedness.solution S a hS (vertical E η) i‖ ≤ (|E| - A - r)⁻¹ := by
  let m := GlobalWellPosedness.solution S a hS (vertical E η)
  have hmpos : 0 < ‖m i‖ := norm_pos_iff.mpr
    (BasicEstimates.component_ne_zero (GlobalWellPosedness.solution_upper a hS
      (z := vertical E η) (by simpa using hη)) i)
  have hd : 0 < |E| - A - r := by linarith
  have hM : ‖m‖ < r⁻¹ := canonical_norm_lt_barrier a hS ha hr hrow hE hη
  have hs : (∑ j, S i j) * ‖m‖ ≤ r := by
    calc
      _ ≤ r ^ 2 * r⁻¹ := mul_le_mul (hrow i) hM.le (norm_nonneg _) (sq_nonneg r)
      _ = r := by field_simp [hr.ne']
  have he := energy_norm_bound hS
    (GlobalWellPosedness.solution_equation a hS (z := vertical E η) (by simpa using hη)) i
  have hinv : |E| - A - r ≤ ‖m i‖⁻¹ := by
    simp only [vertical_re] at he
    linarith [ha i]
  exact (le_inv_comm₀ hd hmpos).mp hinv

theorem imaginary_linear_bound {S : ι → ι → ℝ} {a : ι → ℝ}
    {z : ℂ} {m : ι → ℂ} {d r : ℝ}
    (hS : ∀ i j, 0 ≤ S i j) (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hz : 0 < z.im) (hr : 0 ≤ r) (hdr : r < d)
    (hrow : ∀ i, ∑ j, S i j ≤ r ^ 2)
    (hbound : ∀ i, ‖m i‖ ≤ d⁻¹) (i : ι) :
    (m i).im ≤ (d ^ 2 - r ^ 2)⁻¹ * z.im := by
  classical
  have hd : 0 < d := lt_of_le_of_lt hr hdr
  have hgap : 0 < d ^ 2 - r ^ 2 := by nlinarith
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun k => (m k).im)
    Finset.univ_nonempty
  have hmax : ∀ k, (m k).im ≤ (m j).im := fun k => hj k (Finset.mem_univ k)
  have hy : 0 < (m j).im := hm j
  have hs : (∑ k, S j k * (m k).im) ≤ r ^ 2 * (m j).im := by
    calc
      _ ≤ ∑ k, S j k * (m j).im := Finset.sum_le_sum
        (fun k _ => mul_le_mul_of_nonneg_left (hmax k) (hS j k))
      _ = (∑ k, S j k) * (m j).im := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow j) hy.le
  have hnormpos : 0 < ‖m j‖ := norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm j)
  have hnorm : d * ‖m j‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hbound j) hd.le
    simpa [ne_of_gt hd] using hh
  have hnsq : d ^ 2 * ‖m j‖ ^ 2 ≤ 1 := by
    have hh := mul_le_mul hnorm hnorm (mul_nonneg hd.le (norm_nonneg _))
      (show (0 : ℝ) ≤ 1 by norm_num)
    nlinarith
  have heq := BasicEstimates.imaginary_part_identity_sq_norm hsol j
  have hmult : (m j).im = (z.im + ∑ k, S j k * (m k).im) * ‖m j‖ ^ 2 :=
    (div_eq_iff (pow_ne_zero _ hnormpos.ne')).mp heq
  have hdenpos : 0 ≤ z.im + ∑ k, S j k * (m k).im := by
    exact add_nonneg hz.le (Finset.sum_nonneg (fun k _ => mul_nonneg (hS j k) (hm k).le))
  have hmul := mul_le_mul_of_nonneg_left hnsq hdenpos
  have hdy : d ^ 2 * (m j).im ≤ z.im + ∑ k, S j k * (m k).im := by
    calc
      _ = (z.im + ∑ k, S j k * (m k).im) * (d ^ 2 * ‖m j‖ ^ 2) := by
        rw [hmult]
        ring
      _ ≤ _ := by simpa using hmul
  have hineq : (d ^ 2 - r ^ 2) * (m j).im ≤ z.im := by
    nlinarith [hdy, hs]
  have hjbound : (m j).im ≤ (d ^ 2 - r ^ 2)⁻¹ * z.im := by
    have hh : (m j).im ≤ z.im / (d ^ 2 - r ^ 2) :=
      (le_div_iff₀ hgap).mpr (by nlinarith [hineq])
    simpa [div_eq_mul_inv, mul_comm] using hh
  exact (hmax i).trans hjbound

theorem canonical_exterior_imaginary_bound {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) {A R E : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R)
    (hE : A + 2 * Real.sqrt R < |E|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → ∀ i,
      (GlobalWellPosedness.solution S a hS (vertical E η) i).im ≤ C * η := by
  let r : ℝ := (Real.sqrt R + (|E| - A) / 2) / 2
  have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hsquare : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
  have hr : 0 < r := by dsimp [r]; linarith
  have hsr : Real.sqrt R < r := by dsimp [r]; linarith
  have hEr : A + 2 * r < |E| := by dsimp [r]; linarith
  have hrowr : ∀ i, ∑ j, S i j ≤ r ^ 2 := by
    intro i
    exact (hrow i).trans (by simpa [hsquare] using pow_le_pow_left₀ hsqrt hsr.le 2)
  let d : ℝ := |E| - A - r
  have hdr : r < d := by dsimp [d]; linarith
  have hgap : 0 < d ^ 2 - r ^ 2 := by nlinarith
  refine ⟨(d ^ 2 - r ^ 2)⁻¹, (inv_pos.mpr hgap).le, ?_⟩
  intro η hη i
  simpa only [vertical_im] using imaginary_linear_bound hS
    (GlobalWellPosedness.solution_upper a hS (z := vertical E η) (by simpa using hη))
    (GlobalWellPosedness.solution_equation a hS (z := vertical E η) (by simpa using hη))
    (by simpa using hη) hr.le hdr hrowr
    (canonical_exterior_norm_bound a hS ha hr hrowr hEr hη) i

theorem canonical_normalized {S : ι → ι → ℝ} (a : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j) (i : ι) :
    NormalizedAtInfinity (fun z => GlobalWellPosedness.solution S a hS z i) := by
  intro zs hz hinfty
  exact HighEnergy.normalization_tendsto hS hz
    (fun n => GlobalWellPosedness.solution_upper a hS (hz n))
    (fun n => GlobalWellPosedness.solution_equation a hS (hz n)) hinfty i

/-- Actual probability measures, obtained from generic external representation. -/
theorem canonical_probability_representation (ext : ExternalStieltjesTheory ι)
    {S : ι → ι → ℝ} (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ μ : ι → Measure ℝ, ∀ i, IsProbabilityMeasure (μ i) ∧
      Represents (fun z => GlobalWellPosedness.solution S a hS z i) (μ i) := by
  exact ext.representation (GlobalWellPosedness.solution S a hS)
    (GlobalWellPosedness.solution_analyticOnNhd a hS)
    (fun z hz => GlobalWellPosedness.solution_upper a hS hz)
    (canonical_normalized a hS)

/-- Complete first main theorem, with sharp support radius from row-sum and
potential bounds. The only unproved premises are the explicitly generic
external Stieltjes arguments in `ext`.

Taking `A = maxᵢ |aᵢ|` and `R = maxᵢ ∑ⱼ Sᵢⱼ` gives the sharpened
blueprint radius. Any larger `A`, including the ordinary Euclidean norm
of the potential, gives the manuscript's support radius.
-/
theorem main_theorem_one (ext : ExternalStieltjesTheory ι)
    {S : ι → ι → ℝ} (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (ha : ∀ i, |a i| ≤ A) (hrow : ∀ i, ∑ j, S i j ≤ R) :
    Model.WellPosednessTarget S a ∧
    AnalyticOnNhd ℂ (GlobalWellPosedness.solution S a hS) {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ∀ i, ‖GlobalWellPosedness.solution S a hS z i‖ ≤ z.im⁻¹) ∧
    ∃ μ : ι → Measure ℝ, ∀ i,
      IsProbabilityMeasure (μ i) ∧
      Represents (fun z => GlobalWellPosedness.solution S a hS z i) (μ i) ∧
      μ i (Set.Icc (-(A + 2 * Real.sqrt R)) (A + 2 * Real.sqrt R))ᶜ = 0 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Represents (fun z => GlobalWellPosedness.solution S a hS z i) ν → ν = μ i := by
  refine ⟨GlobalWellPosedness.wellPosednessTarget a hS,
    GlobalWellPosedness.solution_analyticOnNhd a hS,
    fun z hz i => GlobalWellPosedness.solution_norm_le a hS hz i, ?_⟩
  obtain ⟨μ, hμ⟩ := canonical_probability_representation ext a hS
  refine ⟨μ, fun i => ⟨(hμ i).1, (hμ i).2, ?_, ?_⟩⟩
  · apply ext.support_of_poisson_decay _ _ _ (hμ i).1 (hμ i).2
      (by positivity)
    intro E hE
    obtain ⟨C, hC, hc⟩ := canonical_exterior_imaginary_bound a hS hA hR ha hrow hE
    exact ⟨C, hC, fun η hη => hc η hη i⟩
  · intro ν hν hrep
    exact ext.uniqueness _ ν (μ i) hν (hμ i).1 hrep (hμ i).2

/-- For a nonnegative matrix this is exactly its maximum row sum. -/
def maxRowSum (S : ι → ι → ℝ) : ℝ := ‖fun i => ∑ j, S i j‖

def supportRadius (S : ι → ι → ℝ) (a : ι → ℝ) : ℝ :=
  ‖a‖ + 2 * Real.sqrt (maxRowSum S)

/-- The first main theorem with the intrinsic maximum-row-sum support radius;
there are no user-supplied bounds on the coefficients in this version. -/
theorem main_theorem_one_max_norm (ext : ExternalStieltjesTheory ι)
    {S : ι → ι → ℝ} (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    Model.WellPosednessTarget S a ∧
    AnalyticOnNhd ℂ (GlobalWellPosedness.solution S a hS) {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ∀ i, ‖GlobalWellPosedness.solution S a hS z i‖ ≤ z.im⁻¹) ∧
    ∃ μ : ι → Measure ℝ, ∀ i,
      IsProbabilityMeasure (μ i) ∧
      Represents (fun z => GlobalWellPosedness.solution S a hS z i) (μ i) ∧
      μ i (Set.Icc (-(supportRadius S a)) (supportRadius S a))ᶜ = 0 ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Represents (fun z => GlobalWellPosedness.solution S a hS z i) ν → ν = μ i := by
  apply main_theorem_one ext a hS (norm_nonneg a) (norm_nonneg _)
  · intro i
    simpa using norm_le_pi_norm a i
  · intro i
    exact (le_abs_self _).trans (by
      simpa [maxRowSum] using norm_le_pi_norm (fun i => ∑ j, S i j) i)

end NonSymmetricDyson.Full.Foundations
