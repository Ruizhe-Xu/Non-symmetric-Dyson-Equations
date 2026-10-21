import Mathlib
import Dyson.PolynomialDyson
import Dyson.ImaginaryComparability
import Dyson.StripComparability

/-!
# Finite boundary values: equations, nonvanishing, and irreducible comparison

This module passes the actual denominator-free Dyson equations to boundary
limits. No boundary equation or nonvanishing assertion is assumed. The final
comparison uses the already verified finite-matrix irreducibility argument.
The existence of the limits themselves is a separate analytic obligation.
-/

noncomputable section
open scoped BigOperators Topology Matrix
open Filter Set

namespace NonSymmetricDyson.Full.Boundary

open BasicEstimates PolynomialDyson

variable {ι : Type*} [Fintype ι]

/-- The ordinary vertical boundary limit, through positive real heights. -/
def IsBoundaryValue (m : ℂ → ι → ℂ) (τ : ℝ) (b : ι → ℂ) : Prop :=
  Tendsto (fun η : ℝ => m ((τ : ℂ) + (η : ℂ) * Complex.I))
    (𝓝[>] (0 : ℝ)) (𝓝 b)

/-- Polynomial Dyson equations are closed under convergent parameter and
coordinate nets. This statement applies equally to interior and boundary
limits and does not assume that limiting coordinates are nonzero. -/
theorem polynomial_limit {α : Type*} {l : Filter α} [NeBot l]
    (S : ι → ι → ℝ) (a : ι → ℝ)
    {z : α → ℂ} {m : α → ι → ℂ} {z₀ : ℂ} {b : ι → ℂ}
    (hz : Tendsto z l (𝓝 z₀)) (hm : Tendsto m l (𝓝 b))
    (heq : ∀ᶠ t in l, IsPolynomialSolution S a (z t) (m t)) :
    IsPolynomialSolution S a z₀ b := by
  intro i
  have hi (j : ι) : Tendsto (fun t => m t j) l (𝓝 (b j)) :=
    tendsto_pi_nhds.mp hm j
  have hlim : Tendsto (fun t => m t i *
      (z t - (a i : ℂ) + ∑ j, (S i j : ℂ) * m t j)) l
      (𝓝 (b i * (z₀ - (a i : ℂ) + ∑ j, (S i j : ℂ) * b j))) := by
    apply (hi i).mul
    apply (hz.sub tendsto_const_nhds).add
    exact tendsto_finset_sum Finset.univ fun j _ => tendsto_const_nhds.mul (hi j)
  have hconst : Tendsto (fun t => m t i *
      (z t - (a i : ℂ) + ∑ j, (S i j : ℂ) * m t j)) l (𝓝 (-1 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with t ht
    exact ht i
  exact tendsto_nhds_unique hconst hlim

/-- Positivity in the approximating upper-half-plane solutions gives
nonnegativity at a finite limiting boundary point. -/
theorem imaginary_nonnegative_limit {α : Type*} {l : Filter α} [NeBot l]
    {m : α → ι → ℂ} {b : ι → ℂ}
    (hm : Tendsto m l (𝓝 b))
    (hupper : ∀ᶠ t in l, IsUpperSolution (m t)) :
    ∀ i, 0 ≤ (b i).im := by
  intro i
  have hi : Tendsto (fun t => (m t i).im) l (𝓝 (b i).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hm i)
  exact ge_of_tendsto hi (hupper.mono fun t ht => (ht i).le)

/-- The limiting vector is componentwise nonzero because its polynomial
Dyson equation has constant term minus one. -/
theorem boundary_equation_of_limits {α : Type*} {l : Filter α} [NeBot l]
    (S : ι → ι → ℝ) (a : ι → ℝ)
    {z : α → ℂ} {m : α → ι → ℂ} {τ : ℝ} {b : ι → ℂ}
    (hz : Tendsto z l (𝓝 (τ : ℂ))) (hm : Tendsto m l (𝓝 b))
    (heq : ∀ᶠ t in l, IsUpperSolution (m t) ∧ IsDysonSolution S a (z t) (m t)) :
    (∀ i, b i ≠ 0) ∧ (∀ i, 0 ≤ (b i).im) ∧ IsDysonSolution S a (τ : ℂ) b := by
  have hp := polynomial_limit S a hz hm (heq.mono fun t ht =>
    PolynomialDyson.of_dyson ht.2 (BasicEstimates.component_ne_zero ht.1))
  exact ⟨PolynomialDyson.component_ne_zero hp,
    imaginary_nonnegative_limit hm (heq.mono fun t ht => ht.1),
    PolynomialDyson.to_dyson hp⟩

/-- A real-parameter boundary solution satisfies the exact imaginary-part
identity. This version permits zero imaginary parts. -/
theorem boundary_imaginary_identity (S : ι → ι → ℝ) (a : ι → ℝ)
    (τ : ℝ) (b : ι → ℂ) (hb : ∀ i, b i ≠ 0)
    (heq : IsDysonSolution S a (τ : ℂ) b) (i : ι) :
    (b i).im = Complex.normSq (b i) * (∑ j, S i j * (b j).im) := by
  have h := BasicEstimates.imaginary_part_identity heq i
  simp only [Complex.ofReal_im, zero_add] at h
  have hn : Complex.normSq (b i) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr (hb i))
  simpa only [mul_comm] using (div_eq_iff hn).mp h

/-- A finite boundary solution is a nonnegative supersolution for qS
whenever q bounds every squared modulus from below. -/
theorem boundary_supersolution {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (a : Fin n → ℝ) (τ : ℝ) (b : Fin n → ℂ)
    (hb : ∀ i, b i ≠ 0) (hy : ∀ i, 0 ≤ (b i).im)
    (heq : IsDysonSolution S a (τ : ℂ) b)
    (q : ℝ) (hmod : ∀ i, q ≤ Complex.normSq (b i)) :
    ∀ i, ((q • S) *ᵥ (fun j => (b j).im)) i ≤ (b i).im := by
  intro i
  have hsum : 0 ≤ ∑ j, S i j * (b j).im :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hS i j) (hy j)
  have hact : ((q • S) *ᵥ (fun j => (b j).im)) i =
      q * (∑ j, S i j * (b j).im) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_assoc]
  rw [hact, boundary_imaginary_identity S a τ b hb heq i]
  exact mul_le_mul_of_nonneg_right (hmod i) hsum

/-- Uniform irreducible comparison also applies to finite boundary values;
strict imaginary positivity is not needed as an assumption. -/
theorem boundary_comparison {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n → ℝ) (τ : ℝ) (b : Fin n → ℂ),
      (∀ i, b i ≠ 0) → (∀ i, 0 ≤ (b i).im) →
      IsDysonSolution S a (τ : ℂ) b →
      (∀ i, q ≤ Complex.normSq (b i)) →
      ∀ i, C * (∑ j, (b j).im) ≤ (b i).im := by
  have hB : Manuscript.PositivityCorrection.Nonnegative (q • S) := by
    intro i j
    exact mul_nonneg hq.le (hS i j)
  obtain ⟨C, hC, hcomp⟩ :=
    Manuscript.ImaginaryComparability.irreducible_supersolution_comparability
      hn (q • S) hB
      (Manuscript.ImaginaryComparability.irreducible_pos_smul S hirr q hq)
  refine ⟨C, hC, ?_⟩
  intro a τ b hb hy heq hmod i
  exact hcomp (fun j => (b j).im) hy
    (boundary_supersolution S hS a τ b hb hy heq q hmod) i

/-- A finite nonzero vector has a strictly positive common squared-modulus
lower bound; this is proved by a finite minimum, not assumed. -/
theorem exists_positive_normSq_lower {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℂ) (hb : ∀ i, b i ≠ 0) :
    ∃ q : ℝ, 0 < q ∧ ∀ i, q ≤ Complex.normSq (b i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => Complex.normSq (b i)) hne
  exact ⟨Complex.normSq (b i), Complex.normSq_pos.mpr (hb i),
    fun j => hi j (Finset.mem_univ _)⟩

/-- A genuine finite regular boundary solution has either zero density in
all components or strictly positive density in all components. -/
theorem boundary_all_zero_or_all_positive {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a : Fin n → ℝ) (τ : ℝ) (b : Fin n → ℂ)
    (hb : ∀ i, b i ≠ 0) (hy : ∀ i, 0 ≤ (b i).im)
    (heq : IsDysonSolution S a (τ : ℂ) b) :
    (∀ i, (b i).im = 0) ∨ (∀ i, 0 < (b i).im) := by
  classical
  obtain ⟨q, hq, hmod⟩ := exists_positive_normSq_lower hn b hb
  obtain ⟨C, hC, hcomp⟩ := boundary_comparison hn S hS hirr q hq
  by_cases hzero : ∀ i, (b i).im = 0
  · exact Or.inl hzero
  · push_neg at hzero
    obtain ⟨j, hj⟩ := hzero
    have hjpos : 0 < (b j).im := lt_of_le_of_ne (hy j) (Ne.symm hj)
    have hsum : 0 < ∑ k, (b k).im :=
      lt_of_lt_of_le hjpos (Finset.single_le_sum (fun k _ => hy k) (Finset.mem_univ j))
    exact Or.inr fun i => (mul_pos hC hsum).trans_le (hcomp a τ b hb hy heq hmod i)

/-- In particular the positive-density support is independent of the
coordinate at every finite real boundary solution. -/
theorem boundary_positive_iff {n : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (a : Fin n → ℝ) (τ : ℝ) (b : Fin n → ℂ)
    (hb : ∀ i, b i ≠ 0) (hy : ∀ i, 0 ≤ (b i).im)
    (heq : IsDysonSolution S a (τ : ℂ) b) (i j : Fin n) :
    0 < (b i).im ↔ 0 < (b j).im := by
  rcases boundary_all_zero_or_all_positive hn S hS hirr a τ b hb hy heq with hz | hp
  · simp only [hz i, hz j, lt_self_iff_false]
  · exact iff_of_true (hp i) (hp j)

/-- The preceding net theorem applies to the ordinary positive-height limit
of an actual solution family, with no boundary equation assumed. -/
theorem boundary_equation (S : ι → ι → ℝ) (a : ι → ℝ)
    (m : ℂ → ι → ℂ) (τ : ℝ) (b : ι → ℂ)
    (hm : IsBoundaryValue m τ b)
    (hupper : ∀ z : ℂ, 0 < z.im → IsUpperSolution (m z))
    (heq : ∀ z : ℂ, 0 < z.im → IsDysonSolution S a z (m z)) :
    (∀ i, b i ≠ 0) ∧ (∀ i, 0 ≤ (b i).im) ∧ IsDysonSolution S a (τ : ℂ) b := by
  have hcont : Continuous (fun η : ℝ => (τ : ℂ) + (η : ℂ) * Complex.I) := by
    fun_prop
  have hz : Tendsto (fun η : ℝ => (τ : ℂ) + (η : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (τ : ℂ)) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply boundary_equation_of_limits S a hz hm
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hpos : 0 < (((τ : ℂ) + (η : ℂ) * Complex.I).im) := by
    simpa using hη
  exact ⟨hupper _ hpos, heq _ hpos⟩

/-- An interior uniform upper bound passes to a genuine finite boundary
limit. The boundary value is never an arbitrary totalized value. -/
theorem component_upper_bound_limit {α : Type*} {l : Filter α} [NeBot l]
    {m : α → ι → ℂ} {b : ι → ℂ} {M : ℝ}
    (hm : Tendsto m l (𝓝 b))
    (hbound : ∀ᶠ t in l, ∀ i, ‖m t i‖ ≤ M) :
    ∀ i, ‖b i‖ ≤ M := by
  intro i
  exact le_of_tendsto (tendsto_pi_nhds.mp hm i).norm
    (hbound.mono fun t ht => ht i)

/-- Both scaled modulus bounds extend to finite limits. The argument
multiplies by the strictly positive denominator before taking the limit. -/
theorem scaled_bounds_limit {α : Type*} {l : Filter α} [NeBot l]
    {m : α → ι → ℂ} {b : ι → ℂ} {z : α → ℂ} {z₀ : ℂ}
    {L U : ℝ} (hm : Tendsto m l (𝓝 b)) (hz : Tendsto z l (𝓝 z₀))
    (hbound : ∀ᶠ t in l, ∀ i,
      L / (1 + ‖z t‖) ≤ ‖m t i‖ ∧ ‖m t i‖ ≤ U / (1 + ‖z t‖)) :
    ∀ i, L / (1 + ‖z₀‖) ≤ ‖b i‖ ∧ ‖b i‖ ≤ U / (1 + ‖z₀‖) := by
  intro i
  have hlim : Tendsto (fun t => ‖m t i‖ * (1 + ‖z t‖)) l
      (𝓝 (‖b i‖ * (1 + ‖z₀‖))) :=
    (tendsto_pi_nhds.mp hm i).norm.mul (tendsto_const_nhds.add hz.norm)
  have hden : 0 < 1 + ‖z₀‖ := by positivity
  constructor
  · apply (div_le_iff₀ hden).mpr
    apply ge_of_tendsto hlim
    filter_upwards [hbound] with t ht
    exact (div_le_iff₀ (by positivity : 0 < 1 + ‖z t‖)).mp (ht i).1
  · apply (le_div_iff₀ hden).mpr
    apply le_of_tendsto hlim
    filter_upwards [hbound] with t ht
    exact (le_div_iff₀ (by positivity : 0 < 1 + ‖z t‖)).mp (ht i).2

/-- The same interior comparison constant controls the limiting imaginary
parts, including the simultaneous-zero case. -/
theorem imaginary_comparison_limit {α : Type*} {l : Filter α} [NeBot l]
    {m : α → ι → ℂ} {b : ι → ℂ} {C : ℝ}
    (hm : Tendsto m l (𝓝 b))
    (hcomp : ∀ᶠ t in l, ∀ i, C * (∑ j, (m t j).im) ≤ (m t i).im) :
    ∀ i, C * (∑ j, (b j).im) ≤ (b i).im := by
  intro i
  have hi (j : ι) : Tendsto (fun t => (m t j).im) l (𝓝 (b j).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hm j)
  have hleft : Tendsto (fun t => C * ∑ j, (m t j).im) l
      (𝓝 (C * ∑ j, (b j).im)) := tendsto_const_nhds.mul
    (tendsto_finset_sum Finset.univ fun j _ => hi j)
  exact le_of_tendsto_of_tendsto hleft (hi i) (hcomp.mono fun t ht => ht i)

end NonSymmetricDyson.Full.Boundary

namespace NonSymmetricDyson.Full.Boundary

/-- Imaginary part of the angular coefficient in a Puiseux leading term. -/
def angularImag (c : ℂ) (γ θ : ℝ) : ℝ :=
  c.re * Real.sin (γ * θ) + c.im * Real.cos (γ * θ)

theorem angularImag_continuous (c : ℂ) (γ : ℝ) :
    Continuous (angularImag c γ) := by
  unfold angularImag
  fun_prop

theorem angularImag_hasDerivAt (c : ℂ) (γ θ : ℝ) :
    HasDerivAt (angularImag c γ)
      (γ * (c.re * Real.cos (γ * θ) - c.im * Real.sin (γ * θ))) θ := by
  have hs := (Real.hasDerivAt_sin (γ * θ)).comp θ ((hasDerivAt_id θ).const_mul γ)
  have hc := (Real.hasDerivAt_cos (γ * θ)).comp θ ((hasDerivAt_id θ).const_mul γ)
  convert (hs.const_mul c.re).add (hc.const_mul c.im) using 1 <;> ring

/-- An interior angular zero would be a local minimum. Fermat's theorem and
the nonzero leading coefficient rule this out. This proves the strict-ray
part of the manuscript's negative-power lemma inside Lean. -/
theorem angularImag_strict (c : ℂ) (hc : c ≠ 0) (γ : ℝ) (hγ : γ ≠ 0)
    (hnonneg : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, 0 ≤ angularImag c γ θ) :
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi, 0 < angularImag c γ θ := by
  intro θ hθ
  by_contra hpos
  have hz : angularImag c γ θ = 0 := le_antisymm (le_of_not_gt hpos) (hnonneg θ hθ)
  have hmin : IsLocalMin (angularImag c γ) θ := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with x hx
    simpa only [hz] using hnonneg x hx
  have hd : c.re * Real.cos (γ * θ) - c.im * Real.sin (γ * θ) = 0 :=
    (mul_eq_zero.mp (hmin.hasDerivAt_eq_zero (angularImag_hasDerivAt c γ θ))).resolve_left hγ
  have hs : c.re * Real.sin (γ * θ) + c.im * Real.cos (γ * θ) = 0 := hz
  have hre : c.re = 0 := by
    calc
      c.re = c.re * (Real.sin (γ * θ) ^ 2 + Real.cos (γ * θ) ^ 2) := by
        rw [Real.sin_sq_add_cos_sq]; ring
      _ = (c.re * Real.sin (γ * θ) + c.im * Real.cos (γ * θ)) * Real.sin (γ * θ) +
          (c.re * Real.cos (γ * θ) - c.im * Real.sin (γ * θ)) * Real.cos (γ * θ) := by ring
      _ = 0 := by rw [hs, hd]; ring
  have him : c.im = 0 := by
    calc
      c.im = c.im * (Real.sin (γ * θ) ^ 2 + Real.cos (γ * θ) ^ 2) := by
        rw [Real.sin_sq_add_cos_sq]; ring
      _ = (c.re * Real.sin (γ * θ) + c.im * Real.cos (γ * θ)) * Real.cos (γ * θ) -
          (c.re * Real.cos (γ * θ) - c.im * Real.sin (γ * θ)) * Real.sin (γ * θ) := by ring
      _ = 0 := by rw [hs, hd]; ring
  exact hc (Complex.ext hre him)

/-- A negative Puiseux exponent compatible with the Pick sign is at least
minus one. Otherwise two rays less than π apart give opposite coefficients. -/
theorem negative_exponent_ge_neg_one (c : ℂ) (hc : c ≠ 0)
    (γ : ℝ) (hγ : γ < 0)
    (hnonneg : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, 0 ≤ angularImag c γ θ) :
    -1 ≤ γ := by
  by_contra hbound
  have hlarge : 1 < -γ := by linarith
  let δ : ℝ := Real.pi / (-γ)
  have hδpos : 0 < δ := div_pos Real.pi_pos (neg_pos.mpr hγ)
  have hδlt : δ < Real.pi := by
    dsimp [δ]
    apply (div_lt_iff₀ (neg_pos.mpr hγ)).mpr
    nlinarith [Real.pi_pos]
  let θ : ℝ := (Real.pi - δ) / 2
  have hθ : θ ∈ Ioo (0 : ℝ) Real.pi := by
    constructor <;> dsimp [θ] <;> linarith
  have hθ' : θ + δ ∈ Ioo (0 : ℝ) Real.pi := by
    constructor <;> dsimp [θ] <;> linarith
  have hp := angularImag_strict c hc γ (ne_of_lt hγ) hnonneg θ hθ
  have hp' := angularImag_strict c hc γ (ne_of_lt hγ) hnonneg (θ + δ) hθ'
  have hphase : γ * (θ + δ) = γ * θ - Real.pi := by
    dsimp [δ]
    field_simp [ne_of_lt hγ]
    <;> ring
  have hflip : angularImag c γ (θ + δ) = -angularImag c γ θ := by
    unfold angularImag
    rw [hphase, Real.sin_sub_pi, Real.cos_sub_pi]
    ring
  rw [hflip] at hp'
  linarith

/-- At exponent -1, the Pick sign forces the simple-pole coefficient to be
negative real, not merely to have a nonpositive imaginary part. -/
theorem exponent_neg_one_coefficient (c : ℂ) (hc : c ≠ 0)
    (hnonneg : ∀ θ ∈ Ioo (0 : ℝ) Real.pi, 0 ≤ angularImag c (-1) θ) :
    c.im = 0 ∧ c.re < 0 := by
  have hclosed : IsClosed {θ : ℝ | 0 ≤ angularImag c (-1) θ} :=
    isClosed_le continuous_const (angularImag_continuous c (-1))
  have hext : Icc (0 : ℝ) Real.pi ⊆ {θ : ℝ | 0 ≤ angularImag c (-1) θ} := by
    rw [← closure_Ioo (ne_of_lt Real.pi_pos)]
    exact hclosed.closure_subset_iff.mpr hnonneg
  have hleft := hext (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
  have hright := hext (show Real.pi ∈ Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩)
  have him : c.im = 0 := by
    simp [angularImag] at hleft hright
    linarith
  have hmid := angularImag_strict c hc (-1) (by norm_num) hnonneg
    (Real.pi / 2) (by constructor <;> linarith [Real.pi_pos])
  have hcos : Real.cos (-(Real.pi / 2)) = 0 := by simp
  have hsin : Real.sin (-(Real.pi / 2)) = -1 := by simp
  simp only [angularImag, neg_one_mul, him, zero_mul, add_zero, hsin, mul_neg_one] at hmid
  exact ⟨him, by linarith⟩

end NonSymmetricDyson.Full.Boundary
