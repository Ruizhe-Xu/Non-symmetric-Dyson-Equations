import Dyson.Full.BoundaryEdges
import Dyson.Full.BoundaryBounds

/-! Ordinary real continuity and full upper-half-plane limits of the actual
boundary vector near a regular point. The exceptional neighborhood is removed
using the already proved finiteness of the singular union. -/
noncomputable section
open Filter Set
open scoped Topology
namespace NonSymmetricDyson.Full.Boundary
open ExternalAlgebraic
variable {ι : Type*} [Fintype ι]

/-- A regular point has a neighborhood of regular real energies; the actual
boundary function is continuous there and is the full upper limit at each
such energy. -/
theorem regular_boundary_continuous_and_limits
    (algebraic : JacobianAlgebraicity (ι := ι)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (m : ℂ → ι → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ ∉ singularUnion m) :
    ContinuousAt (fun x : ℝ => boundaryVector m (x : ℂ)) τ ∧
      ∀ᶠ x : ℝ in 𝓝 τ, x ∉ singularUnion m ∧
        Tendsto m (𝓝[upper] (x : ℂ)) (𝓝 (boundaryVector m (x : ℂ))) := by
  have hopen : IsOpen (singularUnion m)ᶜ :=
    (family_singular_finite algebraic puiseux S a hS m hupper heq).isClosed.isOpen_compl
  have hregular : ∀ᶠ x : ℝ in 𝓝 τ, x ∉ singularUnion m := hopen.mem_nhds hτ
  have hcont := family_boundary_continuous algebraic puiseux S a hS m hupper heq
  constructor
  · have hc : ContinuousOn (fun x : ℝ => boundaryVector m (x : ℂ)) (singularUnion m)ᶜ :=
      hcont.comp Complex.continuous_ofReal.continuousOn
        (fun x hx => Or.inr ⟨x, hx, rfl⟩)
    exact hc.continuousAt (hopen.mem_nhds hτ)
  · filter_upwards [hregular] with x hx
    refine ⟨hx, ?_⟩
    have hc := hcont (x : ℂ) (Or.inr ⟨x, hx, rfl⟩)
    have ht := (hc.mono (show upper ⊆ commonRegularDomain m from fun _ hz => Or.inl hz)).tendsto
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact family_extension_agrees S a hS m hupper heq z hz

/-- At a regular frontier the same canonical continuous boundary function
has real value at the center. -/
theorem regular_frontier_continuous_and_limits {n : ℕ} (hn : 0 < n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀ z ∈ upper, BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z ∈ upper, BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (i : Fin n) (hfront : τ ∈ frontier (regularSupport m i))
    (hτ : τ ∉ singularUnion m) :
    (∀ j, (boundaryVector m (τ : ℂ) j).im = 0) ∧
    ContinuousAt (fun x : ℝ => boundaryVector m (x : ℂ)) τ ∧
      ∀ᶠ x : ℝ in 𝓝 τ, x ∉ singularUnion m ∧
        Tendsto m (𝓝[upper] (x : ℂ)) (𝓝 (boundaryVector m (x : ℂ))) := by
  exact ⟨regular_frontier_real hn algebraic puiseux S a hS hirr m hupper heq τ i hfront hτ,
    regular_boundary_continuous_and_limits algebraic puiseux S a hS m hupper heq τ hτ⟩

end NonSymmetricDyson.Full.Boundary
