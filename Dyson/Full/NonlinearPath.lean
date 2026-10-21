import Dyson.Full.NonlinearAssembly

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

def rootDenominator (c : ℝ) (k : ℕ) (ω : ℂ) : ℝ :=
  c * (c * ‖ω‖ ^ ((1:ℝ)/k) / 2) ^ (k-1)

theorem rootDenominator_pos (c : ℝ) (hc : 0 < c) (k : ℕ) (ω : ℂ)
    (hω : ω ≠ 0) : 0 < rootDenominator c k ω := by
  dsimp [rootDenominator]
  positivity

/-- The full fine-regime path estimate. The approximate scalar is not assumed
to lie on the physical branch: its index is derived from the product estimate,
connectedness, and one quantitative anchor. -/
theorem reduced_connected_path_bound
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (p q r : ι → ℂ) (k : ℕ) (hk : 0 < k)
    (D : LocalReduction F K ℓ p q r k)
    (ω : X → ℂ) (hg hm R : X → (ι → ℂ))
    (hωcont : Continuous ω) (hgcont : Continuous hg) (hmcont : Continuous hm)
    (hω : ∀ x, 0 < (ω x).im) (hωsmall : ∀ x, ‖ω x‖ < D.rootRadius)
    (hgsmall : ∀ x, ‖hg x‖ < D.radius) (hmsmall : ∀ x, ‖hm x‖ < D.radius)
    (hξg : ∀ x, ‖ω x • (1:ι→ℂ)+R x‖ < D.radius)
    (hξm : ∀ x, ‖ω x • (1:ι→ℂ)‖ < D.radius)
    (heqg : ∀ x, hg x-F (hg x) = quadraticNonlinearity F p q (hg x)
      (ω x • (1:ι→ℂ)+R x))
    (heqm : ∀ x, hm x-F (hm x) = quadraticNonlinearity F p q (hm x)
      (ω x • (1:ι→ℂ)))
    (E A : ℝ) (hE : 0 ≤ E) (hA : 0 < A)
    (hAres : D.residualConstant ≤ A) (hR : ∀ x, ‖R x‖ ≤ E)
    (hgap : ∀ x, 2*(A*E) <
      (D.separation*‖ω x‖^((1:ℝ)/k))*rootDenominator D.separation k (ω x))
    (hden : ∀ x, rootDenominator D.separation k (ω x) ≤ 1)
    (x₀ : X)
    (hanchor : ‖ℓ (hg x₀)-ℓ (hm x₀)‖ ≤
      (A*E)/rootDenominator D.separation k (ω x₀)) :
    ∀ x, ‖q*hg x-q*hm x‖ ≤
      (‖q‖*((‖r‖+D.lipschitzConstant)*A+D.lipschitzConstant))*E /
        rootDenominator D.separation k (ω x) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hω0 : ∀ x, ω x ≠ 0 := by
    intro x hz
    have h := hω x
    simpa [hz] using h
  have hsepcont : Continuous (fun x => D.separation*‖ω x‖^((1:ℝ)/k)) :=
    continuous_const.mul (hωcont.norm.rpow_const (fun x => Or.inl (norm_ne_zero_iff.mpr (hω0 x))))
  have hseppos : ∀ x, 0 < D.separation*‖ω x‖^((1:ℝ)/k) := by
    intro x
    exact mul_pos D.separation_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hω0 x)) _)
  have hredg := fun x => D.reduce (hg x) _ (hgsmall x) (hξg x) (heqg x)
  have hredm := fun x => D.reduce (hm x) _ (hmsmall x) (hξm x) (heqm x)
  have hscalar : ∀ x, ‖ℓ (hg x)-ℓ (hm x)‖ ≤
      (A*E)/rootDenominator D.separation k (ω x) := by
    suffices h : ∀ x, ‖ℓ (hg x)-ℓ (hm x)‖ ≤ (A*E)/
        (D.separation*(D.separation*‖ω x‖^((1:ℝ)/k)/2)^(Fintype.card (Fin k)-1)) by
      simpa only [Fintype.card_fin, rootDenominator] using h
    apply anchored_product_root_bound (x₀ := x₀)
      (fun j x => D.roots j (ω x)) (fun x => ℓ (hg x)) (fun x => ℓ (hm x))
      (fun x θ => spectralScalar F ℓ p q r D.W (θ,ω x))
      (fun x => D.separation*‖ω x‖^((1:ℝ)/k)) D.separation (A*E)
      D.separation_pos (mul_nonneg hA.le hE)
    · intro j
      exact (D.roots_continuous j).comp_continuous hωcont (fun x => ⟨hω x,hωsmall x⟩)
    · exact ℓ.continuous.comp hgcont
    · exact ℓ.continuous.comp hmcont
    · exact hsepcont
    · exact hseppos
    · intro x i j hij
      exact (D.root_data (ω x) (hω x) (hωsmall x)).2 i j hij
    · intro x
      exact D.product_bound (hg x) (ω x) (hgsmall x) (hω x) (hωsmall x)
    · intro x
      exact D.product_bound (hm x) (ω x) (hmsmall x) (hω x) (hωsmall x)
    · intro x
      exact (D.scalar_residual (hg x) (ω x) (R x) (hgsmall x) (hξm x) (hξg x)
        (hredg x).2).trans (mul_le_mul hAres (hR x) (norm_nonneg _) hA.le)
    · intro x
      exact (hredm x).2
    · simpa only [Fintype.card_fin, rootDenominator] using hgap
    · simpa only [Fintype.card_fin, rootDenominator] using hanchor
  intro x
  have hW : ‖D.W (ℓ (hg x),ω x • (1:ι→ℂ)+R x)-
      D.W (ℓ (hm x),ω x • (1:ι→ℂ))‖ ≤
      D.lipschitzConstant*(‖ℓ (hg x)-ℓ (hm x)‖+E) := by
    have h := D.stable_lipschitz (hg x) (hm x) _ _ (hgsmall x) (hmsmall x) (hξg x) (hξm x)
    simp only [add_sub_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_left (hR x) _) D.lipschitzConstant_pos.le)
  exact fine_reconstruction_displacement_bound q r 0 (q*hg x) (q*hm x) _ _
    (ℓ (hg x)) (ℓ (hm x)) D.lipschitzConstant A E
    (rootDenominator D.separation k (ω x)) D.lipschitzConstant_pos.le hA.le hE
    (rootDenominator_pos _ D.separation_pos _ _ (hω0 x)) (hden x)
    (by simpa using congrArg (fun v => q*v) (hredg x).1)
    (by simpa using congrArg (fun v => q*v) (hredm x).1) (hscalar x) hW

end NonSymmetricDyson.Full.Nonlinear
