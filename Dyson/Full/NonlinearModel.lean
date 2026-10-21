import Dyson.Full.NonlinearPath
import Dyson.Full.NonlinearAnchor

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

def normalized (q mτ g : ι → ℂ) : ι → ℂ := (g-mτ)/q

theorem normalized_reconstruction (q mτ g : ι → ℂ) (hq : ∀ i, q i ≠ 0) :
    g = mτ+q*normalized q mτ g := by
  ext i
  simp only [normalized, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
  field_simp [hq i]
  <;> ring

theorem normalized_norm_bound (q mτ g : ι → ℂ) :
    ‖normalized q mτ g‖ ≤ ‖q⁻¹‖*‖g-mτ‖ := by
  change ‖(g-mτ)*q⁻¹‖ ≤ _
  exact (norm_mul_le _ _).trans_eq (mul_comm _ _)

theorem normalized_continuous {X : Type*} [TopologicalSpace X]
    (q mτ : ι → ℂ) (g : X → (ι → ℂ)) (hg : Continuous g) :
    Continuous (fun x => normalized q mτ (g x)) :=
  (hg.sub continuous_const).mul continuous_const

theorem normalized_dyson_residual
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ z : ℂ) (mτ g p q : ι → ℂ)
    (F : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hm : BasicEstimates.IsDysonSolution S a τ mτ)
    (hm0 : ∀ i, mτ i ≠ 0) (hg0 : ∀ i, g i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i^2=1) (hq : ∀ i, q i=p i*mτ i) :
    normalized q mτ g-F (normalized q mτ g) =
      quadraticNonlinearity F p q (normalized q mτ g)
        ((z-τ) • (1:ι→ℂ)+Model.residual S a z g) := by
  have he := actual_normalized_residual S a τ z mτ g p q (normalized q mτ g) F hF
    hm hm0 hg0 hq0 hp hq (normalized_reconstruction q mτ g hq0)
  convert he using 1
  congr 1
  ext i
  simp

/-- The connected-root theorem applied to actual reciprocal Dyson residuals.
Its hypotheses only specify the local domains and a quantitative anchor; no
root membership or scalar residual estimate is supplied by the caller. -/
theorem actual_model_connected_path_bound
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ) (mτ p q r : ι → ℂ)
    (F K : (ι → ℂ) →L[ℂ] (ι → ℂ)) (ℓ : (ι → ℂ) →L[ℂ] ℂ)
    (k : ℕ) (hk : 0 < k) (D : LocalReduction F K ℓ p q r k)
    (hF : (F : (ι → ℂ) → (ι → ℂ)) = DysonPaper.Algebra.scaledOperator q (Model.action S))
    (hmτ : BasicEstimates.IsDysonSolution S a (τ:ℂ) mτ)
    (hmτ0 : ∀ i, mτ i ≠ 0) (hq0 : ∀ i, q i ≠ 0)
    (hp : ∀ i, p i^2=1) (hq : ∀ i, q i=p i*mτ i)
    (z : X → ℂ) (g m : X → (ι → ℂ))
    (hzcont : Continuous z) (hgcont : Continuous g) (hmcont : Continuous m)
    (hz : ∀ x, 0 < (z x).im)
    (hm : ∀ x, BasicEstimates.IsUpperSolution (m x))
    (heqm : ∀ x, BasicEstimates.IsDysonSolution S a (z x) (m x))
    (hg0 : ∀ x i, g x i ≠ 0)
    (hωsmall : ∀ x, ‖z x-(τ:ℂ)‖ < D.rootRadius)
    (hgsmall : ∀ x, ‖normalized q mτ (g x)‖ < D.radius)
    (hmsmall : ∀ x, ‖normalized q mτ (m x)‖ < D.radius)
    (hξg : ∀ x, ‖(z x-(τ:ℂ)) • (1:ι→ℂ)+Model.residual S a (z x) (g x)‖ < D.radius)
    (hξm : ∀ x, ‖(z x-(τ:ℂ)) • (1:ι→ℂ)‖ < D.radius)
    (E A : ℝ) (hE : 0 ≤ E) (hA : 0 < A)
    (hAres : D.residualConstant ≤ A) (hR : ∀ x, ‖Model.residual S a (z x) (g x)‖ ≤ E)
    (hgap : ∀ x, 2*(A*E) < (D.separation*‖z x-(τ:ℂ)‖^((1:ℝ)/k))*
      rootDenominator D.separation k (z x-(τ:ℂ)))
    (hden : ∀ x, rootDenominator D.separation k (z x-(τ:ℂ)) ≤ 1)
    (x₀ : X)
    (hanchor : ‖ℓ (normalized q mτ (g x₀))-ℓ (normalized q mτ (m x₀))‖ ≤
      (A*E)/rootDenominator D.separation k (z x₀-(τ:ℂ))) :
    ∀ x, ‖g x-m x‖ ≤
      (‖q‖*((‖r‖+D.lipschitzConstant)*A+D.lipschitzConstant))*E /
        rootDenominator D.separation k (z x-(τ:ℂ)) := by
  have hzero : ∀ x, Model.residual S a (z x) (m x) = 0 := by
    intro x
    exact (Model.residual_zero_iff S a (z x) (m x)).mpr (heqm x)
  have heqg := fun x => normalized_dyson_residual S a (τ:ℂ) (z x) mτ (g x) p q F hF
    hmτ hmτ0 (hg0 x) hq0 hp hq
  have heqphys : ∀ x, normalized q mτ (m x)-F (normalized q mτ (m x)) =
      quadraticNonlinearity F p q (normalized q mτ (m x)) ((z x-(τ:ℂ)) • (1:ι→ℂ)) := by
    intro x
    simpa only [hzero x, add_zero] using
      normalized_dyson_residual S a (τ:ℂ) (z x) mτ (m x) p q F hF hmτ hmτ0
        (BasicEstimates.component_ne_zero (hm x)) hq0 hp hq
  have h := reduced_connected_path_bound F K ℓ p q r k hk D (fun x => z x-(τ:ℂ))
    (fun x => normalized q mτ (g x)) (fun x => normalized q mτ (m x))
    (fun x => Model.residual S a (z x) (g x)) (hzcont.sub continuous_const)
    (normalized_continuous q mτ g hgcont) (normalized_continuous q mτ m hmcont)
    (fun x => by simpa using hz x) hωsmall hgsmall hmsmall hξg hξm heqg heqphys
    E A hE hA hAres hR hgap hden x₀ hanchor
  intro x
  have hid : q*normalized q mτ (g x)-q*normalized q mτ (m x) = g x-m x := by
    have hg := normalized_reconstruction q mτ (g x) hq0
    have hm := normalized_reconstruction q mτ (m x) hq0
    linear_combination -hg+hm
  simpa only [hid] using h x

end NonSymmetricDyson.Full.Nonlinear
