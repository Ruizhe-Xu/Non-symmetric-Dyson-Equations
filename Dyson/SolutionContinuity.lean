import Mathlib
import Dyson.BasicEstimates
import Dyson.PolynomialDyson
import Dyson.Uniqueness

/-!
Continuity of the actual solution branch.  The proof uses the elementary
norm bound, finite-dimensional compactness, and the proved uniqueness
theorem; no regularity of the branch is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set

namespace NonSymmetricDyson.SolutionContinuity

open BasicEstimates

variable {ι : Type*} [Fintype ι]
variable {S : ι → ι → ℝ} {a : ι → ℝ}

/-- A joint limit of actual solutions remains an actual upper solution when
the limiting spectral parameter stays in the open upper half-plane. -/
theorem solution_of_joint_limit (hS : ∀ i j, 0 ≤ S i j)
    {zs : ℕ → ℂ} {ms : ℕ → ι → ℂ} {z : ℂ} {v : ι → ℂ}
    (hz : 0 < z.im) (hm : ∀ k, IsUpperSolution (ms k))
    (hsol : ∀ k, IsDysonSolution S a (zs k) (ms k))
    (hlimz : Tendsto zs atTop (𝓝 z)) (hlimm : Tendsto ms atTop (𝓝 v)) :
    IsUpperSolution v ∧ IsDysonSolution S a z v := by
  have hlimmi (i : ι) : Tendsto (fun k => ms k i) atTop (𝓝 (v i)) :=
    tendsto_pi_nhds.mp hlimm i
  have hvnonneg : ∀ i, 0 ≤ (v i).im := by
    intro i
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds
      (Complex.continuous_im.continuousAt.tendsto.comp (hlimmi i))
      (fun k => le_of_lt (hm k i))
  have hvpoly : PolynomialDyson.IsPolynomialSolution S a z v := by
    intro i
    have hpolyseq : ∀ k, (-1 : ℂ) = ms k i *
        (zs k - (a i : ℂ) + ∑ j, (S i j : ℂ) * ms k j) := by
      intro k
      exact PolynomialDyson.of_dyson (hsol k) (component_ne_zero (hm k)) i
    have hpolylim : Tendsto (fun k => ms k i *
        (zs k - (a i : ℂ) + ∑ j, (S i j : ℂ) * ms k j)) atTop
        (𝓝 (v i * (z - (a i : ℂ) + ∑ j, (S i j : ℂ) * v j))) := by
      apply (hlimmi i).mul
      apply (hlimz.sub tendsto_const_nhds).add
      exact tendsto_finset_sum Finset.univ fun j _ => tendsto_const_nhds.mul (hlimmi j)
    have hconstlim : Tendsto (fun k => ms k i *
        (zs k - (a i : ℂ) + ∑ j, (S i j : ℂ) * ms k j)) atTop
        (𝓝 (-1 : ℂ)) := by
      have heq : (fun k => ms k i *
          (zs k - (a i : ℂ) + ∑ j, (S i j : ℂ) * ms k j)) =
          fun _ => (-1 : ℂ) := funext fun k => (hpolyseq k).symm
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hconstlim hpolylim
  exact PolynomialDyson.upper_solution_of_polynomial hS hz hvnonneg hvpoly

/-- Solutions converge whenever their spectral parameters converge inside
the upper half-plane.  No continuity assumption on the chosen solutions is needed. -/
theorem solutions_tendsto (hS : ∀ i j, 0 ≤ S i j)
    {zs : ℕ → ℂ} {ms : ℕ → ι → ℂ} {z : ℂ} {m : ι → ℂ}
    (hz : 0 < z.im) (hzs : ∀ k, 0 < (zs k).im)
    (hm : IsUpperSolution m) (hsolm : IsDysonSolution S a z m)
    (hms : ∀ k, IsUpperSolution (ms k))
    (hsolms : ∀ k, IsDysonSolution S a (zs k) (ms k))
    (hlimz : Tendsto zs atTop (𝓝 z)) : Tendsto ms atTop (𝓝 m) := by
  classical
  let R : ℝ := (z.im / 2)⁻¹
  let K : Set (ι → ℂ) := Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) R)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) R
  have hhalf : 0 < z.im / 2 := by positivity
  have himlim : Tendsto (fun k => (zs k).im) atTop (𝓝 z.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimz
  have heta : ∀ᶠ k in atTop, z.im / 2 ≤ (zs k).im :=
    himlim.eventually_const_le (by linarith)
  have hmK : ∀ᶠ k in atTop, ms k ∈ K := heta.mono fun k hk => by
    intro i _
    change dist (ms k i) 0 ≤ R
    rw [dist_zero_right]
    exact (rough_bound hS (hzs k) (hms k) (hsolms k) i).trans
      ((inv_le_inv₀ (hzs k) hhalf).mpr hk)
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨v, _, φ, hφ, hlimv⟩ := hK.tendsto_subseq' (hns.eventually hmK).frequently
  have hzsub : Tendsto (fun k => zs (ns (φ k))) atTop (𝓝 z) :=
    hlimz.comp (hns.comp hφ.tendsto_atTop)
  have hv := solution_of_joint_limit hS hz (fun k => hms (ns (φ k)))
    (fun k => hsolms (ns (φ k))) hzsub hlimv
  have hvm : v = m := Uniqueness.upper_half_plane_unique hS hz hv.1 hm hv.2 hsolm
  exact ⟨φ, hvm ▸ hlimv⟩

/-- Any pointwise chosen family of actual solutions is continuous on the
upper-half-plane subtype.  Global existence can therefore choose the family
without adding a separate continuity assumption. -/
theorem solution_family_continuous (hS : ∀ i j, 0 ≤ S i j)
    (M : {z : ℂ // 0 < z.im} → ι → ℂ)
    (hM : ∀ z : {z : ℂ // 0 < z.im}, IsUpperSolution (M z))
    (hsolM : ∀ z : {z : ℂ // 0 < z.im}, IsDysonSolution S a (z : ℂ) (M z)) :
    Continuous M := by
  apply continuous_iff_seqContinuous.mpr
  intro zs z hlim
  exact solutions_tendsto hS z.property (fun k => (zs k).property)
    (hM z) (hsolM z) (fun k => hM (zs k)) (fun k => hsolM (zs k))
    ((continuous_subtype_val.tendsto z).comp hlim)


end NonSymmetricDyson.SolutionContinuity
