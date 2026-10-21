import Mathlib
import Dyson.BasicEstimates
import Dyson.PolynomialDyson

/-!
The set of spectral parameters admitting an upper-half-plane solution is
closed relative to the upper half-plane.  Compactness is applied to actual
solutions, using the proved elementary norm bound.
-/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.SolutionClosedness

open BasicEstimates

variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ}

/-- Limits inside the open upper half-plane preserve existence of a Dyson solution. -/
theorem solution_exists_of_tendsto (hS : ∀ i j, 0 ≤ S i j)
    {zs : ℕ → ℂ} {z : ℂ} (hz : 0 < z.im)
    (hzs : ∀ k, 0 < (zs k).im) (hlimz : Tendsto zs atTop (𝓝 z))
    (hsol : ∀ k, ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a (zs k) m) :
    ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a z m := by
  classical
  choose m hm using hsol
  let R : ℝ := (z.im / 2)⁻¹
  let K : Set (ι → ℂ) := Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) R)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) R
  have hhalf : 0 < z.im / 2 := by positivity
  have himlim : Tendsto (fun k => (zs k).im) atTop (𝓝 z.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimz
  have heta : ∀ᶠ k in atTop, z.im / 2 ≤ (zs k).im :=
    himlim.eventually_const_le (by linarith)
  have hmK : ∀ᶠ k in atTop, m k ∈ K := heta.mono fun k hk => by
    intro i _
    change dist (m k i) 0 ≤ R
    rw [dist_zero_right]
    exact (rough_bound hS (hzs k) (hm k).1 (hm k).2 i).trans
      ((inv_le_inv₀ (hzs k) hhalf).mpr hk)
  obtain ⟨v, _, φ, hφ, hlimm⟩ := hK.tendsto_subseq' hmK.frequently
  have hlimmi (i : ι) : Tendsto (fun k => m (φ k) i) atTop (𝓝 (v i)) :=
    tendsto_pi_nhds.mp hlimm i
  have hlimzφ : Tendsto (fun k => zs (φ k)) atTop (𝓝 z) :=
    hlimz.comp hφ.tendsto_atTop
  have hvnonneg : ∀ i, 0 ≤ (v i).im := by
    intro i
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      (Complex.continuous_im.continuousAt.tendsto.comp (hlimmi i))
      (fun k => le_of_lt ((hm (φ k)).1 i))
  have hvpoly : PolynomialDyson.IsPolynomialSolution S a z v := by
    intro i
    have hpolyseq : ∀ k, (-1 : ℂ) = m (φ k) i *
        (zs (φ k) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (φ k) j) := by
      intro k
      exact PolynomialDyson.of_dyson (hm (φ k)).2
        (component_ne_zero (hm (φ k)).1) i
    have hpolylim : Tendsto (fun k => m (φ k) i *
        (zs (φ k) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (φ k) j)) atTop
        (𝓝 (v i * (z - (a i : ℂ) + ∑ j, (S i j : ℂ) * v j))) := by
      apply (hlimmi i).mul
      apply (hlimzφ.sub tendsto_const_nhds).add
      exact tendsto_finset_sum Finset.univ fun j _ => tendsto_const_nhds.mul (hlimmi j)
    have hconstlim : Tendsto (fun k => m (φ k) i *
        (zs (φ k) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (φ k) j)) atTop
        (𝓝 (-1 : ℂ)) := by
      have heq : (fun k => m (φ k) i *
          (zs (φ k) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m (φ k) j)) =
          fun _ => (-1 : ℂ) := funext fun k => (hpolyseq k).symm
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hconstlim hpolylim
  exact ⟨v, PolynomialDyson.upper_solution_of_polynomial hS hz hvnonneg hvpoly⟩

/-- The existence set is closed in the upper-half-plane subtype. -/
theorem solution_set_isClosed (hS : ∀ i j, 0 ≤ S i j) :
    IsClosed {z : {z : ℂ // 0 < z.im} |
      ∃ m : ι → ℂ, IsUpperSolution m ∧ IsDysonSolution S a (z : ℂ) m} := by
  apply isSeqClosed_iff_isClosed.mp
  intro zs z hs hlim
  exact solution_exists_of_tendsto hS z.property (fun k => (zs k).property)
    ((continuous_subtype_val.tendsto z).comp hlim) hs


end NonSymmetricDyson.SolutionClosedness
