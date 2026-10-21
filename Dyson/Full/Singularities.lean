import Mathlib
import Dyson.Algebra
import Dyson.PolynomialDyson
import Dyson.LocalSolvability

/-!+# Concrete algebra and analytic interfaces for the singularity proof

This file uses the actual finite-dimensional fields and matrix equations.
In particular the fixed-energy rational family is proved from its displayed
edge and Perron identities, not asserted as an external theorem.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace NonSymmetricDyson.Full.Singularities

section ProjectedResidual

variable {K ι : Type*} [Field K]

/-- The actual normalized Dyson nonlinearity, including vector forcing. -/
def normalizedNonlinearity (F : (ι → K) →ₗ[K] (ι → K))
    (p q h ξ : ι → K) : ι → K :=
  fun i => p i * h i * F h i + q i * (1 + p i * h i) * ξ i

/-- Exact projection equivalence. This uses an inverse only on the stable
complement; in particular it remains valid when the full operator is singular. -/
theorem projected_residual_iff
    (F Kinv : (ι → K) →ₗ[K] (ι → K)) (ℓ : (ι → K) →ₗ[K] K)
    (r h N : ι → K)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hKr : Kinv r = 0)
    (hFr : F r = r)
    (hleft : ∀ x, Kinv (x - F x) = x - ℓ x • r)
    (hright : ∀ x, Kinv x - F (Kinv x) = x - ℓ x • r) :
    h - F h = N ↔ h = ℓ h • r + Kinv N ∧ ℓ N = 0 := by
  constructor
  · intro he
    constructor
    · have hk : Kinv N = h - ℓ h • r := by rw [← he, hleft]
      rw [hk]
      abel
    · rw [← he, map_sub, hlF]
      exact sub_self _
  · rintro ⟨he, hn⟩
    have hh := hright N
    rw [hn, zero_smul, sub_zero] at hh
    conv_lhs => rw [he]
    rw [map_add, map_smul, hFr]
    convert hh using 1 <;> abel

/-- The quadratic and cubic terms of the residual along the second-order
stable approximation are exact finite-vector polynomial identities. -/
theorem nonlinearity_second_order_curve
    (F : (ι → K) →ₗ[K] (ι → K)) (p q r u : ι → K)
    (hFr : F r = r) (θ : K) :
    normalizedNonlinearity F p q (θ • r + θ ^ 2 • u) 0 =
      θ ^ 2 • (fun i => p i * r i ^ 2) +
      θ ^ 3 • (fun i => p i * r i * (u i + F u i)) +
      θ ^ 4 • (fun i => p i * u i * F u i) := by
  ext i
  simp only [normalizedNonlinearity, map_add, map_smul, hFr,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
  ring

end ProjectedResidual

section RestrictedInverse

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Algebraic identities for the inverse on the stable complement. -/
structure IsRestrictedInverse (F Kinv : V →ₗ[K] V) (ℓ : V →ₗ[K] K) (r : V) : Prop where
  kill_right : Kinv r = 0
  kill_left : ∀ x, ℓ (Kinv x) = 0
  left_inverse : ∀ x, Kinv (x - F x) = x - ℓ x • r
  right_inverse : ∀ x, Kinv x - F (Kinv x) = x - ℓ x • r

/-- Construction of the restricted inverse from a simple fixed eigenspace.
This is finite linear algebra, rather than an assumption about Dyson solutions. -/
theorem restricted_inverse_exists [FiniteDimensional K V]
    (F : V →ₗ[K] V) (ℓ : V →ₗ[K] K) (r : V)
    (hnorm : ℓ r = 1) (hFr : F r = r)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r) :
    ∃ Kinv : V →ₗ[K] V, IsRestrictedInverse F Kinv ℓ r := by
  let P : V →ₗ[K] V := LinearMap.id - ℓ.smulRight r
  let L : V →ₗ[K] V := LinearMap.id - F + ℓ.smulRight r
  have hP (x : V) : P x = x - ℓ x • r := rfl
  have hL (x : V) : L x = x - F x + ℓ x • r := rfl
  have hlL (x : V) : ℓ (L x) = ℓ x := by
    rw [hL, map_add, map_sub, map_smul, hlF, hnorm]
    simp
  have hlP (x : V) : ℓ (P x) = 0 := by
    rw [hP, map_sub, map_smul, hnorm]
    simp
  have hzero (x : V) (hx : L x = 0) : x = 0 := by
    have hlx : ℓ x = 0 := by rw [← hlL x, hx, map_zero]
    have hfx : F x = x := by
      rw [hL, hlx, zero_smul, add_zero] at hx
      exact (sub_eq_zero.mp hx).symm
    rw [hsimple x hfx, hlx, zero_smul]
  have hinj : Function.Injective L := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  let e : V ≃ₗ[K] V := LinearEquiv.ofBijective L
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  let Kinv : V →ₗ[K] V := e.symm.toLinearMap.comp P
  have hLK (x : V) : L (Kinv x) = P x := e.apply_symm_apply (P x)
  have hlK (x : V) : ℓ (Kinv x) = 0 := by
    rw [← hlL (Kinv x), hLK, hlP]
  refine ⟨Kinv, ?_, hlK, ?_, ?_⟩
  · apply hinj
    rw [hLK, map_zero, hP, hnorm, one_smul, sub_self]
  · intro x
    apply hinj
    rw [hLK, hP, map_sub, hlF, sub_self, zero_smul, sub_zero,
      hL, map_sub, map_smul, hFr, map_sub, map_smul, hnorm]
    simp only [smul_eq_mul, mul_one, sub_self, zero_smul, add_zero]
    abel
  · intro x
    have hh := hLK x
    rw [hL, hlK, zero_smul, add_zero, hP] at hh
    exact hh

end RestrictedInverse

section RationalFamily

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The exact rational curve used in the nondegeneracy contradiction. -/
def mobiusFamily (m y c : ι → K) (t : K) : ι → K :=
  fun i => m i * (1 - t * c i) / (1 - t * y i)

@[simp] theorem mobiusFamily_zero (m y c : ι → K) :
    mobiusFamily m y c 0 = m := by
  ext i
  simp [mobiusFamily]

/-- All outgoing fractions have the same denominator, by the actual
Jensen-equality edge relation. -/
theorem mobius_sum_factor (S : ι → ι → K) (m y c : ι → K) (t : K)
    (hedge : ∀ i j, S i j ≠ 0 → y j = c i)
    (hy : ∀ j, 1 - t * y j ≠ 0) (i : ι) :
    (1 - t * c i) * (∑ j, S i j * mobiusFamily m y c t j) =
      ∑ j, S i j * m j * (1 - t * c j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : S i j = 0
  · simp [hs]
  · have he := hedge i j hs
    simp only [mobiusFamily]
    rw [← he]
    field_simp [hy j]

/-- The edge relation converts the signed Perron sum into its two moments. -/
theorem signed_perron_sum (S : ι → ι → K) (m y c : ι → K)
    (hedge : ∀ i j, S i j ≠ 0 → y j = c i) (i : ι) :
    (∑ j, S i j * m j * (y j - c j)) =
      c i * (∑ j, S i j * m j) - ∑ j, S i j * m j * c j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hs : S i j = 0
  · simp [hs]
  · rw [hedge i j hs]
    ring

/-- An exact fixed-energy family of polynomial Dyson solutions. Only the
denominators `1-t*y_j` have to be nonzero; nonvanishing of the resulting
solution follows from its polynomial equation. -/
theorem mobius_polynomial_solution (S : ι → ι → K) (b m y c : ι → K)
    (hbase : ∀ i, m i * (b i + ∑ j, S i j * m j) = -1)
    (hperron : ∀ i, y i - c i =
      m i * ∑ j, S i j * m j * (y j - c j))
    (hedge : ∀ i j, S i j ≠ 0 → y j = c i)
    (t : K) (hy : ∀ i, 1 - t * y i ≠ 0) :
    ∀ i, mobiusFamily m y c t i *
      (b i + ∑ j, S i j * mobiusFamily m y c t j) = -1 := by
  intro i
  have hf := mobius_sum_factor S m y c t hedge hy i
  have hp := hperron i
  rw [signed_perron_sum S m y c hedge i] at hp
  have hb := hbase i
  have hc : m i * ((1 - t * c i) * b i +
      ∑ j, S i j * m j * (1 - t * c j)) = -(1 - t * y i) := by
    have hsum : (∑ j, S i j * m j * (1 - t * c j)) =
        (∑ j, S i j * m j) - t * ∑ j, S i j * m j * c j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    linear_combination (1 - t * c i) * hb - t * hp
  have he : m i * ((1 - t * c i) *
      (b i + ∑ j, S i j * mobiusFamily m y c t j)) = -(1 - t * y i) := by
    rw [mul_add, hf]
    exact hc
  calc
    mobiusFamily m y c t i * (b i + ∑ j, S i j * mobiusFamily m y c t j) =
        (m i * ((1 - t * c i) *
          (b i + ∑ j, S i j * mobiusFamily m y c t j))) / (1 - t * y i) := by
      simp only [mobiusFamily]
      ring
    _ = -(1 - t * y i) / (1 - t * y i) := by rw [he]
    _ = -1 := by field_simp [hy i]

end RationalFamily

section ComplexDyson

variable {ι : Type*} [Fintype ι]

/-- The rational family satisfies the actual reciprocal Dyson equation,
at exactly the same energy, with all nonzero coordinates proved. -/
theorem mobius_dyson_solution (S : ι → ι → ℝ) (a : ι → ℝ)
    (τ : ℂ) (m y c : ι → ℂ)
    (hbase : PolynomialDyson.IsPolynomialSolution S a τ m)
    (hperron : ∀ i, y i - c i =
      m i * ∑ j, (S i j : ℂ) * m j * (y j - c j))
    (hedge : ∀ i j, S i j ≠ 0 → y j = c i)
    (t : ℂ) (hy : ∀ i, 1 - t * y i ≠ 0) :
    (∀ i, mobiusFamily m y c t i ≠ 0) ∧
      BasicEstimates.IsDysonSolution S a τ (mobiusFamily m y c t) := by
  have hb : ∀ i, m i * (τ - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j) = -1 :=
    fun i => (hbase i).symm
  have he : ∀ i j, (S i j : ℂ) ≠ 0 → y j = c i := by
    intro i j h
    exact hedge i j (by intro hz; apply h; simp [hz])
  have hp := mobius_polynomial_solution (fun i j => (S i j : ℂ))
    (fun i => τ - (a i : ℂ)) m y c hb hperron he t hy
  have hpoly : PolynomialDyson.IsPolynomialSolution S a τ
      (mobiusFamily m y c t) := fun i => (hp i).symm
  exact ⟨PolynomialDyson.component_ne_zero hpoly,
    PolynomialDyson.to_dyson hpoly⟩

end ComplexDyson

section RationalTangent

variable {ι : Type*} [Fintype ι]

/-- The tangent is computed by the quotient rule, including all factors. -/
theorem mobiusFamily_hasStrictDerivAt (m y c : ι → ℂ) :
    HasStrictDerivAt (mobiusFamily m y c)
      (fun i => m i * (y i - c i)) 0 := by
  apply hasStrictDerivAt_pi.mpr
  intro i
  have hn := ((hasStrictDerivAt_const (0 : ℂ) (1 : ℂ)).sub
    ((hasStrictDerivAt_id (0 : ℂ)).mul_const (c i))).const_mul (m i)
  have hd := (hasStrictDerivAt_const (0 : ℂ) (1 : ℂ)).sub
    ((hasStrictDerivAt_id (0 : ℂ)).mul_const (y i))
  convert hn.div hd (by simp) using 1 <;> simp [mobiusFamily] <;> ring

def perronCoordinate (l q m u : ι → ℂ) : ℂ :=
  ∑ i, l i * ((u i - m i) / q i)

@[simp] theorem perronCoordinate_self (l q m : ι → ℂ) :
    perronCoordinate l q m m = 0 := by simp [perronCoordinate]

/-- The scalar Perron coordinate of the rational family has derivative one. -/
theorem perronCoordinate_mobius_hasStrictDerivAt
    (l q m y c r : ι → ℂ) (hq : ∀ i, q i ≠ 0)
    (htangent : ∀ i, m i * (y i - c i) = q i * r i)
    (hnorm : ∑ i, l i * r i = 1) :
    HasStrictDerivAt (fun t => perronCoordinate l q m (mobiusFamily m y c t)) 1 0 := by
  have hc (i : ι) :=
    ((hasStrictDerivAt_pi.mp (mobiusFamily_hasStrictDerivAt m y c) i).sub
      (hasStrictDerivAt_const (0 : ℂ) (m i))).div_const (q i)
  have hci (i : ι) : HasStrictDerivAt
      (fun t => l i * ((mobiusFamily m y c t i - m i) / q i)) (l i * r i) 0 := by
    convert (hc i).const_mul (l i) using 1
    simp only [sub_zero, htangent]
    field_simp [hq i]
  have hs := HasStrictDerivAt.fun_sum (u := Finset.univ) (fun i _ => hci i)
  simpa only [perronCoordinate, hnorm] using hs

/-- A regular scalar parametrization of a flat solution curve is incompatible
with a convergent sequence of solutions at nonzero energies. The proof is the
ordinary one-dimensional inverse-function theorem, already in Mathlib. -/
theorem flat_graph_contradicts_nonzero_sequence
    (Ω θ : ℂ → ℂ) (hθ0 : θ 0 = 0)
    (hθ : HasStrictDerivAt θ 1 0)
    (hflat : ∀ᶠ t in 𝓝 (0 : ℂ), Ω (θ t) = 0)
    (w ξ : ℕ → ℂ) (hξ : Tendsto ξ atTop (𝓝 0))
    (hw : ∀ n, w n ≠ 0)
    (hgraph : ∀ᶠ n in atTop, w n = Ω (ξ n)) : False := by
  have hz : ∀ᶠ x in 𝓝 (0 : ℂ), Ω x = 0 := by
    have hm : Filter.map θ (𝓝 (0 : ℂ)) = 𝓝 (0 : ℂ) := by
      rw [hθ.map_nhds_eq (by simp), hθ0]
    rw [← hm]
    exact hflat
  have hzseq := hξ.eventually hz
  obtain ⟨n, hn, hzn⟩ := (hgraph.and hzseq).exists
  exact hw n (hn.trans hzn)

/-- The exact Möbius family cannot coexist with a local scalar solution graph
and physical solutions approaching the base point at nonzero energies.
`hgraph` is the explicit conclusion needed from the generic analytic IFT;
no nondegeneracy or classification result is assumed. -/
theorem mobius_obstructs_local_solution_graph
    (S : ι → ι → ℝ) (a : ι → ℝ) (τ : ℂ)
    (m y c q l r : ι → ℂ)
    (hbase : PolynomialDyson.IsPolynomialSolution S a τ m)
    (hperron : ∀ i, y i - c i = m i * ∑ j, (S i j : ℂ) * m j * (y j - c j))
    (hedge : ∀ i j, S i j ≠ 0 → y j = c i)
    (hq : ∀ i, q i ≠ 0)
    (htangent : ∀ i, m i * (y i - c i) = q i * r i)
    (hnorm : ∑ i, l i * r i = 1)
    (Ω : ℂ → ℂ)
    (hgraph : ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 (0, m),
      PolynomialDyson.IsPolynomialSolution S a (τ + v.1) v.2 →
        v.1 = Ω (perronCoordinate l q m v.2))
    (w : ℕ → ℂ) (u : ℕ → ι → ℂ)
    (hwu : Tendsto (fun n => (w n, u n)) atTop (𝓝 (0, m)))
    (hphysical : ∀ n, PolynomialDyson.IsPolynomialSolution S a (τ + w n) (u n))
    (hw : ∀ n, w n ≠ 0) : False := by
  let θ : ℂ → ℂ := fun t => perronCoordinate l q m (mobiusFamily m y c t)
  have hθ0 : θ 0 = 0 := by simp [θ]
  have hθ : HasStrictDerivAt θ 1 0 :=
    perronCoordinate_mobius_hasStrictDerivAt l q m y c r hq htangent hnorm
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i, 1 - t * y i ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).eventually_ne (by simp)
  have hcurve : Tendsto (fun t : ℂ => ((0 : ℂ), mobiusFamily m y c t))
      (𝓝 0) (𝓝 (0, m)) := by
    have hh := (mobiusFamily_hasStrictDerivAt m y c).continuousAt.tendsto
    simp only [mobiusFamily_zero] at hh
    exact tendsto_const_nhds.prodMk_nhds hh
  have hflat : ∀ᶠ t in 𝓝 (0 : ℂ), Ω (θ t) = 0 := by
    filter_upwards [hden, hcurve.eventually hgraph] with t ht hg
    have hs := (mobius_dyson_solution S a τ m y c hbase hperron hedge t ht)
    have hp := PolynomialDyson.of_dyson hs.2 hs.1
    simpa only [θ, add_zero] using (hg (by simpa only [add_zero] using hp)).symm
  have hcoord : Continuous (perronCoordinate l q m) := by
    unfold perronCoordinate
    fun_prop
  have hξ : Tendsto (fun n => perronCoordinate l q m (u n)) atTop (𝓝 0) := by
    have hh := hcoord.continuousAt.tendsto.comp hwu.snd_nhds
    simpa only [perronCoordinate_self] using hh
  apply flat_graph_contradicts_nonzero_sequence Ω θ hθ0 hθ hflat w _ hξ hw
  filter_upwards [hwu.eventually hgraph] with n hn
  exact hn (hphysical n)

end RationalTangent

section AnalyticGraph

variable {ι : Type*} [Fintype ι]

/-- The augmented derivative used to solve energy as a function of the Perron
coordinate. The energy column is retained, so this is invertible even though
the derivative in the vector variable is singular. -/
def augmentedDerivative (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (q : ι → ℂ) :
    (ℂ × (ι → ℂ)) →L[ℂ] (ℂ × (ι → ℂ)) :=
  (ℓ.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).prod
    (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ) -
      F.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)) -
      (ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).smulRight q)

@[simp] theorem augmentedDerivative_apply
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (q : ι → ℂ) (v : ℂ × (ι → ℂ)) :
    augmentedDerivative F ℓ q v = (ℓ v.2, v.2 - F v.2 - v.1 • q) := rfl

theorem augmentedDerivative_bijective
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (q r : ι → ℂ) (hμ : ℓ q ≠ 0)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r) :
    Function.Bijective (augmentedDerivative F ℓ q) := by
  have hinj : Function.Injective (augmentedDerivative F ℓ q).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hl : ℓ v.2 = 0 := congrArg Prod.fst hv
    have hh : v.2 - F v.2 - v.1 • q = 0 := congrArg Prod.snd hv
    have hℓ := congrArg ℓ hh
    simp only [map_sub, map_smul, hlF, sub_self, zero_sub, map_zero,
      smul_eq_mul, neg_eq_zero] at hℓ
    have hw : v.1 = 0 := (mul_eq_zero.mp hℓ).resolve_right hμ
    rw [hw, zero_smul, sub_zero] at hh
    have hu : v.2 = 0 := by
      rw [hsimple v.2 (sub_eq_zero.mp hh).symm, hl, zero_smul]
    exact Prod.ext hw hu
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

def normalizedAugmentedMap (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (p q : ι → ℂ)
    (v : ℂ × (ι → ℂ)) : ℂ × (ι → ℂ) :=
  (ℓ v.2, v.2 - F v.2 - normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1))

theorem normalizedAugmentedMap_zero (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (p q : ι → ℂ) :
    normalizedAugmentedMap F ℓ p q 0 = 0 := by
  ext i <;> simp [normalizedAugmentedMap, normalizedNonlinearity]

theorem normalizedAugmentedMap_analyticAt
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q : ι → ℂ) (v : ℂ × (ι → ℂ)) :
    AnalyticAt ℂ (normalizedAugmentedMap F ℓ p q) v := by
  apply ((ℓ.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).analyticAt v).prod
  apply AnalyticAt.pi
  intro i
  have hc := (LocalSolvability.coordinate (ι := ι) i).analyticAt v
  have hF := ((ContinuousLinearMap.proj i).comp
    (F.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)))).analyticAt v
  have hw := (ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt v
  exact (hc.sub hF).sub (((analyticAt_const.mul hc).mul hF).add
    ((analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul hc))).mul hw))

theorem normalizedAugmentedMap_hasStrictFDerivAt
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q : ι → ℂ) :
    HasStrictFDerivAt (normalizedAugmentedMap F ℓ p q)
      (augmentedDerivative F ℓ q) 0 := by
  apply ((ℓ.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ))).hasStrictFDerivAt).prodMk
  apply hasStrictFDerivAt_pi'.mpr
  intro i
  have hc := (LocalSolvability.coordinate (ι := ι) i).hasStrictFDerivAt
    (x := (0 : ℂ × (ι → ℂ)))
  have hF := ((ContinuousLinearMap.proj i).comp
    (F.comp (ContinuousLinearMap.snd ℂ ℂ (ι → ℂ)))).hasStrictFDerivAt
      (x := (0 : ℂ × (ι → ℂ)))
  have hw := (ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).hasStrictFDerivAt
    (x := (0 : ℂ × (ι → ℂ)))
  have hN := ((hc.const_mul (p i)).fun_mul hF).add
    ((((hc.const_mul (p i)).const_add 1).const_mul (q i)).fun_mul hw)
  convert (hc.sub hF).sub hN using 1 <;>
    simp [normalizedAugmentedMap, normalizedNonlinearity, augmentedDerivative,
      LocalSolvability.coordinate]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.fst,
    ContinuousLinearMap.snd, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A general analytic inverse-function consequence: the zero set of the
second component of a regular augmented map is a scalar analytic graph.
This is proved using Mathlib's inverse-function theorem, without an external
axiom or any assumptions about the desired graph. -/
theorem analytic_graph_of_regular_augmented_map
    (f : (ℂ × (ι → ℂ)) → (ℂ × (ι → ℂ)))
    (e : (ℂ × (ι → ℂ)) ≃L[ℂ] (ℂ × (ι → ℂ)))
    (hf0 : f 0 = 0) (hfa : AnalyticAt ℂ f 0)
    (hfd : HasStrictFDerivAt f (e : _ →L[ℂ] _) 0) :
    ∃ Ω : ℂ → ℂ, AnalyticAt ℂ Ω 0 ∧ Ω 0 = 0 ∧
      ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        (f v).2 = 0 → v.1 = Ω (f v).1 := by
  let inv := hfd.localInverse f e 0
  have hinva : AnalyticAt ℂ inv (f 0) :=
    (hfd.toOpenPartialHomeomorph f).analyticAt_symm'
      hfd.mem_toOpenPartialHomeomorph_source hfa hfd.hasFDerivAt.fderiv
  have hinva0 : AnalyticAt ℂ inv (0 : ℂ × (ι → ℂ)) := by
    simpa only [hf0] using hinva
  have hΩa : AnalyticAt ℂ (fun t : ℂ => (inv (t, 0)).1) 0 :=
    ((ContinuousLinearMap.fst ℂ ℂ (ι → ℂ)).analyticAt _).comp
      (hinva0.comp (f := fun t : ℂ => (t, (0 : ι → ℂ)))
        (analyticAt_id.prod analyticAt_const))
  have hinv0 : inv 0 = 0 := by
    simpa only [hf0] using hfd.localInverse_apply_image
  refine ⟨fun t => (inv (t, 0)).1, hΩa, ?_, ?_⟩
  · exact congrArg Prod.fst hinv0
  · filter_upwards [hfd.eventually_left_inverse] with v hv
    intro hr
    have hp : f v = ((f v).1, 0) := Prod.ext rfl hr
    rw [hp] at hv
    exact (congrArg Prod.fst hv).symm

/-- The actual normalized Dyson residual admits a scalar analytic graph. -/
theorem exists_normalized_analytic_graph
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r) :
    ∃ Ω : ℂ → ℂ, AnalyticAt ℂ Ω 0 ∧ Ω 0 = 0 ∧
      ∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
          v.1 = Ω (ℓ v.2) := by
  have hb := augmentedDerivative_bijective F ℓ q r hμ hlF hsimple
  let e := ContinuousLinearEquiv.ofBijective (augmentedDerivative F ℓ q)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  obtain ⟨Ω, hΩa, hΩ0, hg⟩ := analytic_graph_of_regular_augmented_map
    (normalizedAugmentedMap F ℓ p q) e (normalizedAugmentedMap_zero F ℓ p q)
    (normalizedAugmentedMap_analyticAt F ℓ p q 0)
    (normalizedAugmentedMap_hasStrictFDerivAt F ℓ p q)
  refine ⟨Ω, hΩa, hΩ0, ?_⟩
  filter_upwards [hg] with v hv
  intro hr
  exact hv (sub_eq_zero.mpr hr)

/-- The same inverse-function argument also constructs every point on the
analytic solution curve, rather than only giving a necessary scalar graph. -/
theorem exists_normalized_analytic_parametrization
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (hμ : ℓ q ≠ 0)
    (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r) :
    ∃ curve : ℂ → ℂ × (ι → ℂ), AnalyticAt ℂ curve 0 ∧ curve 0 = 0 ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ℓ (curve θ).2 = θ ∧
        (curve θ).2 - F (curve θ).2 =
          normalizedNonlinearity F.toLinearMap p q (curve θ).2 (fun _ => (curve θ).1)) ∧
      (∀ᶠ v in 𝓝 (0 : ℂ × (ι → ℂ)),
        v.2 - F v.2 = normalizedNonlinearity F.toLinearMap p q v.2 (fun _ => v.1) →
          curve (ℓ v.2) = v) := by
  have hb := augmentedDerivative_bijective F ℓ q r hμ hlF hsimple
  let e := ContinuousLinearEquiv.ofBijective (augmentedDerivative F ℓ q)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  let f := normalizedAugmentedMap F ℓ p q
  have hf0 : f 0 = 0 := normalizedAugmentedMap_zero F ℓ p q
  have hfa : AnalyticAt ℂ f 0 := normalizedAugmentedMap_analyticAt F ℓ p q 0
  have hfd : HasStrictFDerivAt f (e : _ →L[ℂ] _) 0 :=
    normalizedAugmentedMap_hasStrictFDerivAt F ℓ p q
  let inv := hfd.localInverse f e 0
  have hinva : AnalyticAt ℂ inv (f 0) :=
    (hfd.toOpenPartialHomeomorph f).analyticAt_symm'
      hfd.mem_toOpenPartialHomeomorph_source hfa hfd.hasFDerivAt.fderiv
  have hinva0 : AnalyticAt ℂ inv (0 : ℂ × (ι → ℂ)) := by simpa only [hf0] using hinva
  have hcurve : AnalyticAt ℂ (fun θ : ℂ => inv (θ, 0)) 0 :=
    hinva0.comp (f := fun θ : ℂ => (θ, (0 : ι → ℂ))) (analyticAt_id.prod analyticAt_const)
  have hinv0 : inv 0 = 0 := by simpa only [hf0] using hfd.localInverse_apply_image
  have hembed : Tendsto (fun θ : ℂ => (θ, (0 : ι → ℂ))) (𝓝 0) (𝓝 (f 0)) := by
    rw [hf0]
    exact continuousAt_id.prodMk continuousAt_const
  refine ⟨fun θ => inv (θ, 0), hcurve, hinv0, ?_, ?_⟩
  · filter_upwards [hembed.eventually hfd.eventually_right_inverse] with θ hθ
    refine ⟨congrArg Prod.fst hθ, ?_⟩
    exact sub_eq_zero.mp (congrArg Prod.snd hθ)
  · filter_upwards [hfd.eventually_left_inverse] with v hv
    intro hres
    have hp : f v = (ℓ v.2, 0) := Prod.ext rfl (sub_eq_zero.mpr hres)
    rw [hp] at hv
    exact hv

/-- Passing from the actual Dyson polynomial equations to the exact normalized
residual, with all nonzero coordinates and changes of variables checked. -/
theorem polynomial_solution_normalized_residual
    (S : ι → ι → ℝ) (a : ι → ℝ) (τ w : ℂ)
    (m g p q : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hq0 : ∀ i, q i ≠ 0)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hm : PolynomialDyson.IsPolynomialSolution S a τ m)
    (hg : PolynomialDyson.IsPolynomialSolution S a (τ + w) g) :
    let h : ι → ℂ := fun i => (g i - m i) / q i
    h - F h = normalizedNonlinearity F.toLinearMap p q h (fun _ => w) := by
  intro h
  have hgm : g = m + DysonPaper.Algebra.coordMul q h := by
    ext i
    simp only [Pi.add_apply, DysonPaper.Algebra.coordMul, h]
    field_simp [hq0 i]
    ring
  have hs := DysonPaper.Algebra.normalized_quadratic_equation
    m g (fun i => τ - (a i : ℂ)) (fun _ => w) p q h (Model.action S)
    (PolynomialDyson.component_ne_zero hm) (PolynomialDyson.component_ne_zero hg)
    hq0 hp hq hgm (PolynomialDyson.to_dyson hm) ?_
  · simpa only [← hF h, normalizedNonlinearity, ContinuousLinearMap.coe_coe] using hs
  · intro i
    have hh := PolynomialDyson.to_dyson hg i
    change -(g i)⁻¹ = τ - (a i : ℂ) + Model.action S g i + w
    rw [Model.action_apply]
    linear_combination hh

end AnalyticGraph

section DysonGraph

variable {ι : Type*} [Fintype ι]

theorem exists_dyson_analytic_graph
    (S : ι → ι → ℝ) (a : ι → ℝ) (τ : ℂ)
    (m p q r l : ι → ℂ) (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hq0 : ∀ i, q i ≠ 0)
    (hF : ∀ h, F h = DysonPaper.Algebra.scaledOperator q (Model.action S) h)
    (hℓ : ∀ h, ℓ h = ∑ i, l i * h i)
    (hμ : ℓ q ≠ 0) (hlF : ∀ x, ℓ (F x) = ℓ x)
    (hsimple : ∀ x, F x = x → x = ℓ x • r)
    (hm : PolynomialDyson.IsPolynomialSolution S a τ m) :
    ∃ Ω : ℂ → ℂ, AnalyticAt ℂ Ω 0 ∧ Ω 0 = 0 ∧
      ∀ᶠ v : ℂ × (ι → ℂ) in 𝓝 (0, m),
        PolynomialDyson.IsPolynomialSolution S a (τ + v.1) v.2 →
          v.1 = Ω (perronCoordinate l q m v.2) := by
  obtain ⟨Ω, hΩa, hΩ0, hg⟩ := exists_normalized_analytic_graph F ℓ p q r hμ hlF hsimple
  let normalize : (ℂ × (ι → ℂ)) → (ℂ × (ι → ℂ)) :=
    fun v => (v.1, fun i => (v.2 i - m i) / q i)
  have hn : Continuous normalize := by unfold normalize; fun_prop
  have hn0 : normalize (0, m) = 0 := by ext i <;> simp [normalize]
  have ht : Tendsto normalize (𝓝 (0, m)) (𝓝 0) := by
    simpa only [hn0] using hn.continuousAt.tendsto (x := (0, m))
  refine ⟨Ω, hΩa, hΩ0, ?_⟩
  filter_upwards [ht.eventually hg] with v hv
  intro hsol
  have he := hv (polynomial_solution_normalized_residual S a τ v.1 m v.2 p q F
    hp hq hq0 hF hm hsol)
  simpa only [normalize, hℓ, perronCoordinate] using he

end DysonGraph

section MarkovVariance

variable {ι : Type*} [Fintype ι]

/-- One row of the Markov variance identity, including its mean relation. -/
theorem row_variance_identity (Q y : ι → ℝ) (c : ℝ)
    (hrow : ∑ j, Q j = 1) (hmean : ∑ j, Q j * y j = c) :
    (∑ j, Q j * (y j - c) ^ 2) = (∑ j, Q j * y j ^ 2) - c ^ 2 := by
  calc
    (∑ j, Q j * (y j - c) ^ 2) =
      ∑ j, (Q j * y j ^ 2 - (2 * c) * (Q j * y j) + c ^ 2 * Q j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = (∑ j, Q j * y j ^ 2) - (2 * c) * (∑ j, Q j * y j) +
        c ^ 2 * (∑ j, Q j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hmean, hrow]; ring

/-- Full finite stationary Markov variance identity. -/
theorem stationary_variance_identity (Q : ι → ι → ℝ) (π y c : ι → ℝ)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i * Q i j = π j)
    (hmean : ∀ i, ∑ j, Q i j * y j = c i) :
    (∑ i, π i * y i ^ 2) - (∑ i, π i * c i ^ 2) =
      ∑ i, ∑ j, π i * Q i j * (y j - c i) ^ 2 := by
  symm
  calc
    (∑ i, ∑ j, π i * Q i j * (y j - c i) ^ 2) =
        ∑ i, π i * ((∑ j, Q i j * y j ^ 2) - c i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← row_variance_identity (Q i) y (c i) (hrow i) (hmean i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, π i * Q i j * y j ^ 2) - ∑ i, π i * c i ^ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    _ = (∑ j, (∑ i, π i * Q i j) * y j ^ 2) - ∑ i, π i * c i ^ 2 := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp only [hstat]

/-- Equality in Jensen forces the edgewise equality used in the exact
rational family. No irreducibility or spectral theorem is hidden here. -/
theorem stationary_variance_zero_edge (Q : ι → ι → ℝ) (π y c : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hπ : ∀ i, 0 < π i)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i * Q i j = π j)
    (hmean : ∀ i, ∑ j, Q i j * y j = c i)
    (hzero : (∑ i, π i * y i ^ 2) - (∑ i, π i * c i ^ 2) = 0) :
    ∀ i j, 0 < Q i j → y j = c i := by
  have hs : (∑ i, ∑ j, π i * Q i j * (y j - c i) ^ 2) = 0 := by
    rw [← stationary_variance_identity Q π y c hrow hstat hmean]
    exact hzero
  have hnonneg : ∀ i j, 0 ≤ π i * Q i j * (y j - c i) ^ 2 := by
    intro i j
    exact mul_nonneg (mul_nonneg (hπ i).le (hQ i j)) (sq_nonneg _)
  intro i j hij
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Finset.sum_nonneg (fun l _ => hnonneg k l))).mp hs i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => hnonneg i k)).mp hi j (Finset.mem_univ j)
  have hsq : (y j - c i) ^ 2 = 0 :=
    (mul_eq_zero.mp hj).resolve_left (mul_ne_zero (hπ i).ne' hij.ne')
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- The cubic Markov form is nonnegative for every contraction parameter
between zero and one, including periodic/nonreversible chains. -/
theorem stationary_contraction_nonnegative (Q : ι → ι → ℝ) (π y c : ι → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hπ : ∀ i, 0 ≤ π i)
    (hrow : ∀ i, ∑ j, Q i j = 1)
    (hstat : ∀ j, ∑ i, π i * Q i j = π j)
    (hmean : ∀ i, ∑ j, Q i j * y j = c i)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    0 ≤ (∑ i, π i * y i ^ 2) - lam ^ 2 * (∑ i, π i * c i ^ 2) := by
  have hv : 0 ≤ (∑ i, π i * y i ^ 2) - (∑ i, π i * c i ^ 2) := by
    rw [stationary_variance_identity Q π y c hrow hstat hmean]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hπ i) (hQ i j)) (sq_nonneg _)
  have hc : 0 ≤ ∑ i, π i * c i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hπ i) (sq_nonneg _)
  have hlam : 0 ≤ 1 - lam ^ 2 := by nlinarith
  have hh := mul_nonneg hlam hc
  nlinarith

end MarkovVariance

section CubicCoefficient

variable {ι : Type*} [Fintype ι]

def markovKernel (F : ι → ι → ℝ) (r : ι → ℝ) (i j : ι) : ℝ :=
  F i j * r j / r i

def stationaryWeight (l r : ι → ℝ) (i : ι) : ℝ := l i * r i

def quadraticCoefficient (p l r : ι → ℝ) : ℝ := ∑ i, l i * p i * r i ^ 2

def cubicCoefficient (F : ι → ι → ℝ) (p l r u : ι → ℝ) : ℝ :=
  ∑ i, p i * l i * r i * (u i + ∑ j, F i j * u j)

theorem markovKernel_row_sum (F : ι → ι → ℝ) (r : ι → ℝ)
    (hr : ∀ i, r i ≠ 0) (hFr : ∀ i, ∑ j, F i j * r j = r i) (i : ι) :
    ∑ j, markovKernel F r i j = 1 := by
  simp only [markovKernel, ← Finset.sum_div, hFr, div_self (hr i)]

theorem stationaryWeight_stationary (F : ι → ι → ℝ) (l r : ι → ℝ)
    (hr : ∀ i, r i ≠ 0) (hlF : ∀ j, ∑ i, l i * F i j = l j) (j : ι) :
    ∑ i, stationaryWeight l r i * markovKernel F r i j = stationaryWeight l r j := by
  calc
    (∑ i, stationaryWeight l r i * markovKernel F r i j) =
        ∑ i, (l i * F i j) * r j := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [stationaryWeight, markovKernel]
      field_simp [hr i]
    _ = _ := by rw [← Finset.sum_mul, hlF]; rfl

theorem markovKernel_mean (F : ι → ι → ℝ) (r u : ι → ℝ)
    (hr : ∀ i, r i ≠ 0) (i : ι) :
    (∑ j, markovKernel F r i j * (u j / r j)) =
      (∑ j, F i j * u j) / r i := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [markovKernel]
  field_simp [hr i, hr j]

/-- The paper's cubic coefficient is exactly the stationary variance when
the quadratic coefficient vanishes. The hypothesis on `u` is the restricted
inverse equation `(I-F)u=pr²`, obtained when `σ=0`. -/
theorem cubicCoefficient_eq_variance
    (F : ι → ι → ℝ) (p l r u : ι → ℝ)
    (hr : ∀ i, r i ≠ 0)
    (hu : ∀ i, u i - ∑ j, F i j * u j = p i * r i ^ 2) :
    cubicCoefficient F p l r u =
      (∑ i, stationaryWeight l r i * (u i / r i) ^ 2) -
      (∑ i, stationaryWeight l r i * ((∑ j, F i j * u j) / r i) ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [cubicCoefficient, stationaryWeight]
  have hi := hu i
  field_simp [hr i]
  linear_combination -(l i * (u i + ∑ j, F i j * u j)) * hi

/-- Nonnegativity of the actual cubic coefficient follows from Jensen, with
no reversibility or aperiodicity assumption. -/
theorem cubicCoefficient_nonnegative
    (F : ι → ι → ℝ) (p l r u : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j)
    (hu : ∀ i, u i - ∑ j, F i j * u j = p i * r i ^ 2) :
    0 ≤ cubicCoefficient F p l r u := by
  rw [cubicCoefficient_eq_variance F p l r u (fun i => (hr i).ne') hu]
  simpa only [one_pow, one_mul] using stationary_contraction_nonnegative
    (markovKernel F r) (stationaryWeight l r) (fun i => u i / r i)
    (fun i => (∑ j, F i j * u j) / r i)
    (fun i j => div_nonneg (mul_nonneg (hF i j) (hr j).le) (hr i).le)
    (fun i => (mul_pos (hl i) (hr i)).le)
    (markovKernel_row_sum F r (fun i => (hr i).ne') hFr)
    (stationaryWeight_stationary F l r (fun i => (hr i).ne') hlF)
    (markovKernel_mean F r u (fun i => (hr i).ne')) 1 (by norm_num) (by norm_num)

/-- Vanishing of the actual cubic coefficient forces the precise edge
relation of the Möbius-family construction. -/
theorem cubicCoefficient_zero_edge
    (F : ι → ι → ℝ) (p l r u : ι → ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j)
    (hu : ∀ i, u i - ∑ j, F i j * u j = p i * r i ^ 2)
    (hψ : cubicCoefficient F p l r u = 0) :
    ∀ i j, 0 < F i j → u j / r j = (∑ k, F i k * u k) / r i := by
  have hz := hψ
  rw [cubicCoefficient_eq_variance F p l r u (fun i => (hr i).ne') hu] at hz
  have he := stationary_variance_zero_edge
    (markovKernel F r) (stationaryWeight l r) (fun i => u i / r i)
    (fun i => (∑ j, F i j * u j) / r i)
    (fun i j => div_nonneg (mul_nonneg (hF i j) (hr j).le) (hr i).le)
    (fun i => mul_pos (hl i) (hr i))
    (markovKernel_row_sum F r (fun i => (hr i).ne') hFr)
    (stationaryWeight_stationary F l r (fun i => (hr i).ne') hlF)
    (markovKernel_mean F r u (fun i => (hr i).ne')) hz
  intro i j hij
  exact he i j (div_pos (mul_pos hij (hr j)) (hr i))

/-- The second-order eigenvalue coefficient obtained from simple-eigenvalue
perturbation agrees with `2(ψ-σ²)`. This calculation uses the restricted
inverse equation and is specific to the Dyson cubic coefficient. -/
theorem cubic_spectral_coefficient_identity
    (F : ι → ι → ℝ) (p l r u : ι → ℝ)
    (hp : ∀ i, p i ^ 2 = 1)
    (hu : ∀ i, u i - ∑ j, F i j * u j =
      p i * r i ^ 2 - r i * quadraticCoefficient p l r) :
    4 * (∑ i, p i * l i * r i * u i) - 2 * (∑ i, l i * r i ^ 3) =
      2 * (cubicCoefficient F p l r u - (quadraticCoefficient p l r) ^ 2) := by
  have he : cubicCoefficient F p l r u =
      2 * (∑ i, p i * l i * r i * u i) - (∑ i, l i * r i ^ 3) +
        (quadraticCoefficient p l r) ^ 2 := by
    have hs : (quadraticCoefficient p l r) ^ 2 =
        ∑ i, (p i * l i * r i ^ 2) * quadraticCoefficient p l r := by
      rw [← Finset.sum_mul]
      have hσ : (∑ i, p i * l i * r i ^ 2) = quadraticCoefficient p l r := by
        unfold quadraticCoefficient
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hσ]
      ring
    rw [hs, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi := hu i
    have hpterm : p i ^ 2 * l i * r i ^ 3 = l i * r i ^ 3 := by rw [hp, one_mul]
    linear_combination -(p i * l i * r i) * hi - hpterm
  rw [he]
  ring

end CubicCoefficient

section Nondegeneracy

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def complexMatrixOperator (F : ι → ι → ℝ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (Model.action F).toContinuousLinearMap

def complexFunctional (l : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (l i : ℂ) • ContinuousLinearMap.proj i

@[simp] theorem complexFunctional_apply (l : ι → ℝ) (x : ι → ℂ) :
    complexFunctional l x = ∑ i, (l i : ℂ) * x i := by
  simp [complexFunctional]

@[simp] theorem complexMatrixOperator_apply (F : ι → ι → ℝ) (x : ι → ℂ) (i : ι) :
    complexMatrixOperator F x i = ∑ j, (F i j : ℂ) * x j := rfl

theorem complexFunctional_left_eigenvector (F : ι → ι → ℝ) (l : ι → ℝ)
    (hlF : ∀ j, ∑ i, l i * F i j = l j) (x : ι → ℂ) :
    complexFunctional l (complexMatrixOperator F x) = complexFunctional l x := by
  simp only [complexFunctional_apply, complexMatrixOperator_apply]
  calc
    (∑ i, (l i : ℂ) * ∑ j, (F i j : ℂ) * x j) =
        ∑ i, ∑ j, ((l i : ℂ) * (F i j : ℂ)) * x j := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ j, (∑ i, ((l i : ℂ) * (F i j : ℂ))) * x j := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact_mod_cast hlF j

theorem signed_perron_identity
    (S F : ι → ι → ℝ) (m p q r : ι → ℝ)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hF : ∀ i j, F i j = q i * S i j * q j)
    (hFr : ∀ i, ∑ j, F i j * r j = r i) (i : ι) :
    p i * r i = m i * ∑ j, S i j * m j * (p j * r j) := by
  have hpq : p i * q i = m i := by
    calc
      p i * q i = p i ^ 2 * m i := by rw [hq]; ring
      _ = m i := by rw [hp, one_mul]
  calc
    p i * r i = p i * ∑ j, F i j * r j := by rw [hFr]
    _ = (p i * q i) * ∑ j, S i j * q j * r j := by
      simp only [Finset.mul_sum, hF]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = m i * ∑ j, S i j * m j * (p j * r j) := by
      rw [hpq]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hq]
      ring

/-- Dyson-specific nondegeneracy. Here `u` is the stable inverse applied to
`pr²`, as expressed by its displayed equation. All other matrix hypotheses
are Perron normalization, positivity, and simple fixed eigenspace. The
conclusion is derived from the exact rational curve and the physical sequence;
neither nondegeneracy nor any singularity classification is an input. -/
theorem singularity_coefficients_nondegenerate
    (S F : ι → ι → ℝ) (a : ι → ℝ) (τ : ℂ)
    (m p q r l u : ι → ℝ)
    (hS : ∀ i j, 0 ≤ S i j)
    (hp : ∀ i, p i ^ 2 = 1) (hq : ∀ i, q i = p i * m i)
    (hqpos : ∀ i, 0 < q i) (hr : ∀ i, 0 < r i) (hl : ∀ i, 0 < l i)
    (hF : ∀ i j, F i j = q i * S i j * q j)
    (hFr : ∀ i, ∑ j, F i j * r j = r i)
    (hlF : ∀ j, ∑ i, l i * F i j = l j)
    (hnorm : ∑ i, l i * r i = 1)
    (hsimple : ∀ x : ι → ℂ, complexMatrixOperator F x = x →
      x = complexFunctional l x • (fun i => (r i : ℂ)))
    (hu : ∀ i, u i - ∑ j, F i j * u j =
      p i * r i ^ 2 - r i * quadraticCoefficient p l r)
    (hbase : PolynomialDyson.IsPolynomialSolution S a τ (fun i => (m i : ℂ)))
    (w : ℕ → ℂ) (g : ℕ → ι → ℂ)
    (hphysical : ∀ n, PolynomialDyson.IsPolynomialSolution S a (τ + w n) (g n))
    (hconv : Tendsto (fun n => (w n, g n)) atTop (𝓝 (0, fun i => (m i : ℂ))))
    (hw : ∀ n, w n ≠ 0) :
    quadraticCoefficient p l r ≠ 0 ∨ 0 < cubicCoefficient F p l r u := by
  by_cases hσ : quadraticCoefficient p l r = 0
  · right
    have hu0 : ∀ i, u i - ∑ j, F i j * u j = p i * r i ^ 2 := by
      simpa only [hσ, mul_zero, sub_zero] using hu
    have hFpos : ∀ i j, 0 ≤ F i j := by
      intro i j
      rw [hF]
      exact mul_nonneg (mul_nonneg (hqpos i).le (hS i j)) (hqpos j).le
    have hψnonneg := cubicCoefficient_nonnegative F p l r u hFpos hl hr hFr hlF hu0
    apply lt_of_le_of_ne hψnonneg
    intro hz
    have hψ : cubicCoefficient F p l r u = 0 := hz.symm
    let y : ι → ℝ := fun i => u i / r i
    let c : ι → ℝ := fun i => (∑ j, F i j * u j) / r i
    have hdiff (i : ι) : y i - c i = p i * r i := by
      dsimp [y, c]
      rw [← sub_div, hu0]
      field_simp [(hr i).ne']
    have hedge : ∀ i j, S i j ≠ 0 → y j = c i := by
      intro i j hij
      apply cubicCoefficient_zero_edge F p l r u hFpos hl hr hFr hlF hu0 hψ i j
      rw [hF]
      exact mul_pos (mul_pos (hqpos i) (lt_of_le_of_ne (hS i j) (Ne.symm hij))) (hqpos j)
    have hperron (i : ι) : y i - c i = m i * ∑ j, S i j * m j * (y j - c j) := by
      simp only [hdiff]
      exact signed_perron_identity S F m p q r hp hq hF hFr i
    have htangent (i : ι) : m i * (y i - c i) = q i * r i := by
      rw [hdiff, hq]
      ring
    have hμR : 0 < ∑ i, l i * q i :=
      Finset.sum_pos (fun i _ => mul_pos (hl i) (hqpos i)) Finset.univ_nonempty
    have hμ : complexFunctional l (fun i => (q i : ℂ)) ≠ 0 := by
      rw [complexFunctional_apply]
      exact_mod_cast hμR.ne'
    have hFcomplex (h : ι → ℂ) : complexMatrixOperator F h =
        DysonPaper.Algebra.scaledOperator (fun i => (q i : ℂ)) (Model.action S) h := by
      ext i
      simp only [complexMatrixOperator_apply, DysonPaper.Algebra.scaledOperator,
        DysonPaper.Algebra.coordMul, Model.action_apply, hF, Complex.ofReal_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    obtain ⟨Ω, _, _, hgraph⟩ := exists_dyson_analytic_graph S a τ
      (fun i => (m i : ℂ)) (fun i => (p i : ℂ)) (fun i => (q i : ℂ))
      (fun i => (r i : ℂ)) (fun i => (l i : ℂ)) (complexMatrixOperator F)
      (complexFunctional l) (fun i => by dsimp only; exact_mod_cast hp i)
      (fun i => by dsimp only; exact_mod_cast hq i) (fun i => by dsimp only; exact_mod_cast (hqpos i).ne')
      hFcomplex (complexFunctional_apply l) hμ (complexFunctional_left_eigenvector F l hlF)
      hsimple hbase
    exact mobius_obstructs_local_solution_graph S a τ (fun i => (m i : ℂ))
      (fun i => (y i : ℂ)) (fun i => (c i : ℂ)) (fun i => (q i : ℂ))
      (fun i => (l i : ℂ)) (fun i => (r i : ℂ)) hbase
      (fun i => by dsimp only; exact_mod_cast hperron i)
      (fun i j hij => by dsimp only; exact_mod_cast hedge i j hij)
      (fun i => by dsimp only; exact_mod_cast (hqpos i).ne')
      (fun i => by dsimp only; exact_mod_cast htangent i) (by dsimp only; exact_mod_cast hnorm)
      Ω hgraph w g hconv hphysical hw
  · exact Or.inl hσ

end Nondegeneracy

section PhysicalRootSelection

/-- The physical square-root branch is uniquely determined by positive
imaginary part, including arbitrary complex forcing in the upper half-plane. -/
theorem square_root_upper_unique (s t : ℂ) (hs : 0 < s.im) (ht : 0 < t.im)
    (heq : s ^ 2 = t ^ 2) : s = t := by
  have hf : (s - t) * (s + t) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.zero_im] at hi
    linarith

/-- An upper-half-plane root of a cubic whose value lies in the lower
half-plane lies in the central cone. This is an exact sign calculation. -/
theorem cubic_upper_central_cone (s : ℂ) (hs : 0 < s.im)
    (hcube : (s ^ 3).im < 0) : 3 * s.re ^ 2 < s.im ^ 2 := by
  have he : (s ^ 3).im = s.im * (3 * s.re ^ 2 - s.im ^ 2) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  rw [he] at hcube
  have hh : 3 * s.re ^ 2 - s.im ^ 2 < 0 := by
    by_contra h
    have hm := mul_nonneg hs.le (le_of_not_gt h)
    linarith
  linarith

/-- The cusp has exactly one possible physical cubic branch. No appeal to
branch labels or a picture of the roots is needed. -/
theorem cubic_root_upper_unique (s t : ℂ)
    (hs : 0 < s.im) (ht : 0 < t.im)
    (hvalue : (s ^ 3).im < 0) (heq : s ^ 3 = t ^ 3) : s = t := by
  have hscone := cubic_upper_central_cone s hs hvalue
  have htcone := cubic_upper_central_cone t ht (by rw [← heq]; exact hvalue)
  have hfactor : (s - t) * (s ^ 2 + s * t + t ^ 2) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, pow_two, Complex.mul_re, Complex.zero_re] at hre
    have hcross : 0 < s.im * t.im := mul_pos hs ht
    nlinarith [sq_nonneg (s.re - t.re)]

/-- For the cusp coefficient `c=-ψ/μ<0`, positive spectral imaginary part
puts the cubic value in the lower half-plane, so the physical branch is unique. -/
theorem cusp_physical_branch_unique (c : ℝ) (hc : c < 0) (w s t : ℂ)
    (hw : 0 < w.im) (hs : 0 < s.im) (ht : 0 < t.im)
    (hsroot : (c : ℂ) * s ^ 3 = w) (htroot : (c : ℂ) * t ^ 3 = w) : s = t := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne
  have heq : s ^ 3 = t ^ 3 := mul_left_cancel₀ hc0 (hsroot.trans htroot.symm)
  apply cubic_root_upper_unique s t hs ht _ heq
  have hi := congrArg Complex.im hsroot
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hi
  nlinarith

end PhysicalRootSelection

end NonSymmetricDyson.Full.Singularities
