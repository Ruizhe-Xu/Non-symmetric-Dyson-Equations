import Dyson.Full.MainSingularityDensity

/-! Topological identification of the quadratic and cubic alternatives.
An edge has exactly one local side in the regular support; a cusp has both
punctured sides. These definitions use the actual support set. -/

noncomputable section
open Filter Set
open scoped Topology

namespace NonSymmetricDyson.Full.Singularities

/-- A local endpoint: in a neighborhood the open support is exactly one of
the two sides of the point. The sign chooses left or right. -/
def IsRegularEdge (U : Set ℝ) (τ : ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∀ᶠ x in 𝓝 τ, (x ∈ U ↔ c * (x - τ) < 0)

/-- An interior touching point: both punctured sides are in the regular
support, while the point itself is outside it. -/
def IsRegularCusp (U : Set ℝ) (τ : ℝ) : Prop :=
  ∀ᶠ x in 𝓝 τ, (x ∈ U ↔ x ≠ τ)

theorem edge_not_cusp {U : Set ℝ} {τ : ℝ}
    (he : IsRegularEdge U τ) : ¬ IsRegularCusp U τ := by
  rintro hc
  obtain ⟨c, hc0, hedge⟩ := he
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hedge.and hc)
  by_cases hp : 0 < c
  · let x := τ + ε / 2
    have hx : dist x τ < ε := by
      rw [Real.dist_eq]
      dsimp [x]
      rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
      linarith
    have hne : x ≠ τ := by dsimp [x]; linarith
    have hm := (hball hx).2.mpr hne
    have hnegative := (hball hx).1.mp hm
    have hpositive : 0 < c * (x - τ) := mul_pos hp (by dsimp [x]; linarith)
    linarith
  · have hn : c < 0 := lt_of_le_of_ne (le_of_not_gt hp) hc0
    let x := τ - ε / 2
    have hx : dist x τ < ε := by
      rw [Real.dist_eq]
      have heq : x - τ = -(ε / 2) := by dsimp [x]; ring
      rw [heq, abs_neg, abs_of_pos (half_pos hε)]
      linarith
    have hne : x ≠ τ := by dsimp [x]; linarith
    have hm := (hball hx).2.mpr hne
    have hnegative := (hball hx).1.mp hm
    have hpositive : 0 < c * (x - τ) := mul_pos_of_neg_of_neg hn (by dsimp [x]; linarith)
    linarith

theorem cusp_not_edge {U : Set ℝ} {τ : ℝ}
    (hc : IsRegularCusp U τ) : ¬ IsRegularEdge U τ := fun he => edge_not_cusp he hc

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The quadratic physical normal form identifies a genuine one-sided support
endpoint, rather than merely a square-root asymptotic at an unnamed point. -/
theorem PhysicalNormalForm.quadratic_isRegularEdge
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) (hk : P.degree = 2) (i : ι)
    (hb0 : Boundary.boundaryVector m (τ : ℂ) = (fun j => (m₀ j : ℂ)))
    (hbcont : ContinuousAt (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ,
      Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (Boundary.boundaryVector m (x : ℂ))))
    (hregular : ∀ᶠ x : ℝ in 𝓝 τ, x ∉ Boundary.singularUnion m) :
    IsRegularEdge (Boundary.regularSupport m i) τ := by
  have hτnot : τ ∉ Boundary.regularSupport m i := by
    intro h
    have hh := h.2
    rw [hb0] at hh
    simpa using hh
  refine ⟨P.coefficient, P.coefficient_ne_zero, ?_⟩
  filter_upwards [P.quadratic_boundary_density hk
    (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont hblim, hregular]
    with x hx hreg
  constructor
  · intro hmem
    by_contra hn
    have hnonnegative : 0 ≤ P.coefficient * (x - τ) := le_of_not_gt hn
    rcases eq_or_lt_of_le hnonnegative with hz | hp
    · have hprod : P.coefficient * (x - τ) = 0 := hz.symm
      have hxt : x = τ := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left P.coefficient_ne_zero)
      exact hτnot (hxt ▸ hmem)
    · exact (ne_of_gt hmem.2) ((hx i).2 hp)
  · intro hside
    exact ⟨hreg, ((hx i).1 hside).2⟩

/-- The cubic physical normal form identifies an actual two-sided cusp. -/
theorem PhysicalNormalForm.cubic_isRegularCusp
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) (hk : P.degree = 3) (i : ι)
    (hb0 : Boundary.boundaryVector m (τ : ℂ) = (fun j => (m₀ j : ℂ)))
    (hbcont : ContinuousAt (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ,
      Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (Boundary.boundaryVector m (x : ℂ))))
    (hregular : ∀ᶠ x : ℝ in 𝓝 τ, x ∉ Boundary.singularUnion m) :
    IsRegularCusp (Boundary.regularSupport m i) τ := by
  have hτnot : τ ∉ Boundary.regularSupport m i := by
    intro h
    have hh := h.2
    rw [hb0] at hh
    simpa using hh
  filter_upwards [P.cubic_boundary_density hk
    (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) hb0 hbcont hblim, hregular]
    with x hx hreg
  exact ⟨fun hm he => hτnot (he ▸ hm), fun hne => ⟨hreg, (hx i).2 hne⟩⟩

/-- For an actual physical chart, its analytic degree is equivalent to the
local support topology, in both directions. -/
theorem PhysicalNormalForm.degree_iff_support_topology
    {S : Matrix ι ι ℝ} {a : ι → ℝ} {τ : ℝ}
    {m : ℂ → ι → ℂ} {m₀ : ι → ℝ}
    (P : PhysicalNormalForm S a τ m m₀) (i : ι)
    (hb0 : Boundary.boundaryVector m (τ : ℂ) = (fun j => (m₀ j : ℂ)))
    (hbcont : ContinuousAt (fun x : ℝ => Boundary.boundaryVector m (x : ℂ)) τ)
    (hblim : ∀ᶠ x : ℝ in 𝓝 τ,
      Tendsto m (𝓝[ExternalAlgebraic.upper] (x : ℂ)) (𝓝 (Boundary.boundaryVector m (x : ℂ))))
    (hregular : ∀ᶠ x : ℝ in 𝓝 τ, x ∉ Boundary.singularUnion m) :
    (P.degree = 2 ↔ IsRegularEdge (Boundary.regularSupport m i) τ) ∧
    (P.degree = 3 ↔ IsRegularCusp (Boundary.regularSupport m i) τ) := by
  have he := fun hk => P.quadratic_isRegularEdge hk i hb0 hbcont hblim hregular
  have hc := fun hk => P.cubic_isRegularCusp hk i hb0 hbcont hblim hregular
  constructor
  · refine ⟨he, ?_⟩
    intro hedge
    rcases P.degree_cases with hk | hk
    · exact hk
    · exact False.elim (edge_not_cusp hedge (hc hk))
  · refine ⟨hc, ?_⟩
    intro hcusp
    rcases P.degree_cases with hk | hk
    · exact False.elim (cusp_not_edge hcusp (he hk))
    · exact hk

/-- Topological degree identification for a chart at an actual regular
frontier, with all boundary-continuity hypotheses discharged. -/
theorem regular_frontier_degree_iff_support_topology
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (P : PhysicalNormalForm S a τ m (fun j => (Boundary.boundaryVector m (τ : ℂ) j).re)) :
    (P.degree = 2 ↔ IsRegularEdge (Boundary.regularSupport m i) τ) ∧
    (P.degree = 3 ↔ IsRegularCusp (Boundary.regularSupport m i) τ) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  have hb0 : Boundary.boundaryVector m (τ : ℂ) =
      (fun j => ((Boundary.boundaryVector m (τ : ℂ) j).re : ℂ)) := by
    ext j
    apply Complex.ext
    · rfl
    · simpa using Boundary.regular_frontier_real hn algebraic puiseux S a hS hirr m
        hupper heq τ i hfront hτ j
  obtain ⟨hbcont, hblocal⟩ := Boundary.regular_boundary_continuous_and_limits
    algebraic puiseux S a hS m hupper heq τ hτ
  exact P.degree_iff_support_topology i hb0 hbcont
    (hblocal.mono fun _ h => h.2) (hblocal.mono fun _ h => h.1)

/-- Every actual regular frontier is exactly one of an edge and a cusp. -/
theorem regular_frontier_topological_dichotomy
    (perron : ExternalPerronExistence)
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    (IsRegularEdge (Boundary.regularSupport m i) τ ∧ ¬ IsRegularCusp (Boundary.regularSupport m i) τ) ∨
      (¬ IsRegularEdge (Boundary.regularSupport m i) τ ∧ IsRegularCusp (Boundary.regularSupport m i) τ) := by
  obtain ⟨P⟩ := regular_frontier_physical_normal_form perron normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ
  have hd := regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P
  rcases P.degree_cases with hk | hk
  · exact Or.inl ⟨hd.1.mp hk, edge_not_cusp (hd.1.mp hk)⟩
  · exact Or.inr ⟨cusp_not_edge (hd.2.mp hk), hd.2.mp hk⟩

/-- The exact quadratic coefficient in any supplied actual frontier data
vanishes precisely at a two-sided cusp. This connects the data used by M7
to the same support topology used by M5 and M6. -/
theorem frontier_coefficient_iff_support_topology
    (normalForm : RealAnalyticMonomialNormalFormPrinciple)
    (orientation : RealHolomorphicOrientationPrinciple)
    {n : ℕ} (hn : 0 < n)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m)
    (d : FrontierData S (Boundary.boundaryVector m (τ : ℂ))) :
    (quadraticCoefficient d.p d.l d.r ≠ 0 ↔ IsRegularEdge (Boundary.regularSupport m i) τ) ∧
    (quadraticCoefficient d.p d.l d.r = 0 ↔ IsRegularCusp (Boundary.regularSupport m i) τ) := by
  obtain ⟨P, hquad, hcubic⟩ := frontier_data_physical_normal_form normalForm orientation hn
    algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ d
  have ht := regular_frontier_degree_iff_support_topology hn algebraic puiseux S a hS hirr
    m hupper heq τ i hfront hτ P
  constructor
  · refine ⟨fun h => ht.1.mp (hquad h), ?_⟩
    intro hedge hzero
    exact edge_not_cusp hedge (ht.2.mp (hcubic hzero))
  · refine ⟨fun h => ht.2.mp (hcubic h), ?_⟩
    intro hcusp
    by_contra hn
    exact cusp_not_edge hcusp (ht.1.mp (hquad hn))

end NonSymmetricDyson.Full.Singularities
