import Dyson.Full.MainNonlinear
import Dyson.Full.SingularitiesFrontierData
import Dyson.Full.BoundaryBounds

/-! M7 at actual regular frontier points. All Perron, restricted inverse,
Taylor coefficient, and nondegeneracy data are obtained from the actual
boundary vector. Only the explicitly generic external principles remain. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear
open Singularities

variable {n : ℕ}

def frontierScale (m₀ : Fin n → ℂ) : Fin n → ℂ := fun i => (‖m₀ i‖ : ℂ)

/-- The common regular extension is continuous on the closed half-plane near
a regular point, since the finite singular set can be avoided locally. -/
theorem regular_extension_continuousWithinAt
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ Boundary.singularUnion m) :
    ContinuousWithinAt (Boundary.boundaryVector m) {z : ℂ | 0 ≤ z.im} (τ : ℂ) := by
  have hopen : IsOpen (Boundary.singularUnion m)ᶜ :=
    (Boundary.family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
  have hreal : ∀ᶠ z : ℂ in 𝓝 (τ : ℂ), z.re ∉ Boundary.singularUnion m :=
    (Complex.continuous_re.continuousAt (x := (τ : ℂ))).tendsto.eventually
      (by simpa using hopen.mem_nhds hτ)
  have hdom : Boundary.commonRegularDomain m ∈ 𝓝[{z : ℂ | 0 ≤ z.im}] (τ : ℂ) := by
    filter_upwards [hreal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz him
    rcases lt_or_eq_of_le him with hpos | hzero
    · exact Or.inl hpos
    · refine Or.inr ⟨z.re, hz, ?_⟩
      apply Complex.ext
      · simp
      · simpa using hzero
  exact (Boundary.family_boundary_continuous algebraic puiseux S a hS m hupper heq
    (τ : ℂ) (Or.inr ⟨τ, hτ, rfl⟩)).mono_of_mem_nhdsWithin hdom

theorem frontier_scale_identity
    {S : Matrix (Fin n) (Fin n) ℝ} {m₀ : Fin n → ℂ} (d : FrontierData S m₀) :
    (∀ i, frontierScale m₀ i ≠ 0) ∧
    (∀ i, (d.p i : ℂ) ^ 2 = 1) ∧
    ∀ i, frontierScale m₀ i = (d.p i : ℂ) * m₀ i := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (‖m₀ i‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (d.nonzero i)
  · intro i
    exact_mod_cast d.sign_square i
  · intro i
    apply Complex.ext
    · simpa [frontierScale, Complex.mul_re, d.real_value] using d.norm_sign i
    · simp [frontierScale, Complex.mul_im, d.real_value]

theorem frontier_operator_scaled (S : Matrix (Fin n) (Fin n) ℝ) (m₀ : Fin n → ℂ) :
    (complexMatrixOperator (saturatedMatrix S m₀) : (Fin n → ℂ) → (Fin n → ℂ)) =
      DysonPaper.Algebra.scaledOperator (frontierScale m₀) (Model.action S) := by
  funext h i
  change (∑ j, (saturatedMatrix S m₀ i j : ℂ) * h j) = _
  simp only [saturatedMatrix, Complex.ofReal_mul,
    DysonPaper.Algebra.scaledOperator, DysonPaper.Algebra.coordMul,
    Model.action_apply, Finset.mul_sum, frontierScale]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The degree and local reduction are constructed from actual frontier data.
In particular the quadratic/cubic estimates are not theorem hypotheses. -/
theorem frontier_localReduction_exists [Nonempty (Fin n)]
    (ift : AnalyticImplicitFunctionPrinciple (Fin n → ℂ) (ℂ × (Fin n → ℂ)))
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (S : Matrix (Fin n) (Fin n) ℝ) (m₀ : Fin n → ℂ) (d : FrontierData S m₀) :
    ∃ k : ℕ,
      ((k = 2 ∧ quadraticCoefficient d.p d.l d.r ≠ 0) ∨
       (k = 3 ∧ quadraticCoefficient d.p d.l d.r = 0 ∧
         0 < cubicCoefficient (saturatedMatrix S m₀) d.p d.l d.r d.u)) ∧
      Nonempty (LocalReduction (complexMatrixOperator (saturatedMatrix S m₀))
        d.K.toContinuousLinearMap (complexFunctional d.l)
        (fun i => (d.p i : ℂ)) (frontierScale m₀) (fun i => (d.r i : ℂ)) k) := by
  let F := complexMatrixOperator (saturatedMatrix S m₀)
  let K := d.K.toContinuousLinearMap
  let ℓ := complexFunctional d.l
  let p : Fin n → ℂ := fun i => (d.p i : ℂ)
  let q := frontierScale m₀
  let r : Fin n → ℂ := fun i => (d.r i : ℂ)
  have hFr : F r = r := by
    ext i
    simp only [F, r, complexMatrixOperator_apply]
    exact_mod_cast d.right_fixed i
  have hlF : ∀ x, ℓ (F x) = ℓ x :=
    complexFunctional_left_eigenvector (saturatedMatrix S m₀) d.l d.left_fixed
  have hμ : ℓ q ≠ 0 := by
    have hsum : 0 < ∑ i, d.l i * ‖m₀ i‖ :=
      Finset.sum_pos (fun i _ => mul_pos (d.left_positive i)
        (norm_pos_iff.mpr (d.nonzero i))) Finset.univ_nonempty
    have heq : ℓ q = ((∑ i, d.l i * ‖m₀ i‖ : ℝ) : ℂ) := by
      simp [ℓ, q, frontierScale, complexFunctional_apply]
    rw [heq]
    exact_mod_cast hsum.ne'
  have hσ : ℓ (p * r * r) = (quadraticCoefficient d.p d.l d.r : ℂ) := by
    simpa only [ℓ, p, r, pow_two, mul_assoc] using d.quadratic_bridge
  have hψ : ℓ (p * r * (F (K (p * r * r)) + K (p * r * r))) =
      (cubicCoefficient (saturatedMatrix S m₀) d.p d.l d.r d.u : ℂ) := by
    simpa only [ℓ, p, r, F, K, pow_two, mul_assoc] using d.cubic_bridge
  by_cases hquad : quadraticCoefficient d.p d.l d.r = 0
  · have hcubic : 0 < cubicCoefficient (saturatedMatrix S m₀) d.p d.l d.r d.u :=
      d.nondegenerate.resolve_left (not_ne_iff.mpr hquad)
    refine ⟨3, Or.inr ⟨rfl, hquad, hcubic⟩, ?_⟩
    apply localReduction_exists ift rootArgument F K ℓ p q r hFr hlF d.restricted
      3 (cubicCoefficient (saturatedMatrix S m₀) d.p d.l d.r d.u : ℂ)
      (by exact_mod_cast hcubic.ne') hμ
    exact Or.inr ⟨rfl, by rw [hσ, hquad]; simp, hψ.symm⟩
  · refine ⟨2, Or.inl ⟨rfl, hquad⟩, ?_⟩
    apply localReduction_exists ift rootArgument F K ℓ p q r hFr hlF d.restricted
      2 (quadraticCoefficient d.p d.l d.r : ℂ) (by exact_mod_cast hquad) hμ
    exact Or.inl ⟨rfl, hσ.symm⟩

/-- M7(iii) at every actual regular frontier. The continuation endpoint may be
any height above the fixed anchor. Constants are chosen before the energy,
height, residual size, endpoint, and approximate family. The degree certificate
records the exact edge/cusp coefficient alternative derived at the frontier. -/
theorem main_theorem_seven_regular_frontier_below
    (Hmax : ℝ) (hHmax : 0 < Hmax)
    (external : ExternalPerronExistence)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (ift : AnalyticImplicitFunctionPrinciple (Fin n → ℂ) (ℂ × (Fin n → ℂ)))
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ d : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    ∃ k : ℕ, ∃ H r c₀ C : ℝ,
      ((k = 2 ∧ quadraticCoefficient d.p d.l d.r ≠ 0) ∨
       (k = 3 ∧ quadraticCoefficient d.p d.l d.r = 0 ∧
         0 < cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)))
           d.p d.l d.r d.u)) ∧
      0 < H ∧ H ≤ Hmax ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → Fin n → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ (1 - (1 : ℝ) / k) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨d⟩ := regular_frontier_data external hn algebraic puiseux S a hS hirr m
    hupper heq τ i hfront hτ
  let m₀ := Boundary.boundaryVector m (τ : ℂ)
  let mbar := Boundary.boundaryVector m
  obtain ⟨k, hcase, ⟨D⟩⟩ := frontier_localReduction_exists ift rootArgument S m₀ d
  have hk : 2 ≤ k := by rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _, _⟩ <;> omega
  obtain ⟨hq0, hp, hq⟩ := frontier_scale_identity d
  have hboundary := Boundary.family_boundary_equation algebraic puiseux S a hS m hupper heq τ hτ
  have hmcont : ContinuousWithinAt mbar {z : ℂ | 0 ≤ z.im} (τ : ℂ) :=
    regular_extension_continuousWithinAt algebraic puiseux S a hS m hupper heq τ hτ
  have hbar : ∀ z : ℂ, 0 < z.im → mbar z = m z :=
    Boundary.family_extension_agrees S a hS m hupper heq
  obtain ⟨H, r, c₀, C, hH, hHmax', hr, hc₀, hC, hbound⟩ :=
    nonlinear_boundary_main_of_reduction_below Hmax hHmax S a hS τ mbar m₀ (fun j => (d.p j : ℂ))
      (frontierScale m₀) (fun j => (d.r j : ℂ))
      (complexMatrixOperator (saturatedMatrix S m₀)) d.K.toContinuousLinearMap
      (complexFunctional d.l) k hk D (frontier_operator_scaled S m₀)
      hboundary.2.2 d.nonzero hq0 hp hq rfl hmcont
      (fun z hz => by rw [hbar z hz]; exact hupper z hz)
      (fun z hz => by rw [hbar z hz]; exact heq z hz)
  refine ⟨d, k, H, r, c₀, C, hcase, hH, hHmax', hr, hc₀, hC, ?_⟩
  intro x η η₀ E g htop hx hη hηH hE hgcont hg0 hclose hres
  have hsub : Icc η H ⊆ Icc η η₀ := fun t ht => ⟨ht.1, ht.2.trans htop⟩
  have hpositive : ∀ t ∈ Icc η H, 0 < (verticalPoint x t).im :=
    fun t ht => hη.trans_le ht.1
  have hh := hbound x η E g hx hη hηH hE (hgcont.mono hsub)
    (fun t ht => hg0 t (hsub ht))
    (fun t ht => by rw [hbar _ (hpositive t ht)]; exact hclose t (hsub ht))
    (fun t ht => hres t (hsub ht))
  rw [hbar _ hη] at hh
  exact hh

/-- The uniform high-anchor statement without a prescribed height cap. -/
theorem main_theorem_seven_regular_frontier
    (external : ExternalPerronExistence)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := Fin n))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (ift : AnalyticImplicitFunctionPrinciple (Fin n → ℂ) (ℂ × (Fin n → ℂ)))
    (rootArgument : AnalyticRootFactorizationPrinciple)
    (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ ExternalAlgebraic.upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (Boundary.regularSupport m i))
    (hτ : τ ∉ Boundary.singularUnion m) :
    ∃ d : FrontierData S (Boundary.boundaryVector m (τ : ℂ)),
    ∃ k : ℕ, ∃ H r c₀ C : ℝ,
      ((k = 2 ∧ quadraticCoefficient d.p d.l d.r ≠ 0) ∨
       (k = 3 ∧ quadraticCoefficient d.p d.l d.r = 0 ∧
         0 < cubicCoefficient (saturatedMatrix S (Boundary.boundaryVector m (τ : ℂ)))
           d.p d.l d.r d.u)) ∧
      0 < H ∧ 0 < r ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ (x η η₀ E : ℝ) (g : ℝ → Fin n → ℂ),
        H ≤ η₀ → |x - τ| ≤ r → 0 < η → η ≤ H → 0 ≤ E →
        ContinuousOn g (Icc η η₀) →
        (∀ t ∈ Icc η η₀, ∀ j, g t j ≠ 0) →
        (∀ t ∈ Icc η η₀, ‖g t - m (verticalPoint x t)‖ ≤ c₀) →
        (∀ t ∈ Icc η η₀, ‖Model.residual S a (verticalPoint x t) (g t)‖ ≤ E) →
        ‖g η - m (verticalPoint x η)‖ ≤
          C * E / (E + ‖verticalPoint x η - (τ : ℂ)‖) ^ (1 - (1 : ℝ) / k) := by
  obtain ⟨d,k,H,r,c₀,C,hcase,hH,_,hr,hc₀,hC,hb⟩ :=
    main_theorem_seven_regular_frontier_below 1 zero_lt_one external algebraic puiseux ift rootArgument
      hn S a hS hirr m hupper heq τ i hfront hτ
  exact ⟨d,k,H,r,c₀,C,hcase,hH,hr,hc₀,hC,hb⟩

end NonSymmetricDyson.Full.Nonlinear
