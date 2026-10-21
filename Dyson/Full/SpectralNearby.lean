import Dyson.Full.SpectralUniform
import Dyson.Full.PerronVarying

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities Spectral PerronContinuation

/-- The actual normalized imaginary coordinate tends to zero at a nonzero
real limiting solution; this includes approaches along the closed half-plane. -/
theorem normalizedImag_tendsto_zero {X ι : Type*} [Fintype ι]
    (L : Filter X) (m : X → ι → ℂ) (m₀ : ι → ℂ)
    (hm : Tendsto m L (𝓝 m₀)) (hreal : ∀ i, (m₀ i).im=0)
    (hnz : ∀ i, m₀ i≠0) (i : ι) :
    Tendsto (fun x => normalizedImag (m x) i) L (𝓝 0) := by
  have ht : Tendsto (fun x => m x i) L (𝓝 (m₀ i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hm
  have h := (Complex.continuous_im.continuousAt.tendsto.comp ht).div ht.norm
    (norm_ne_zero_iff.mpr (hnz i))
  simpa [normalizedImag,hreal i] using h

theorem perronDensity_tendsto_zero {X ι : Type*} [Fintype ι]
    (L : Filter X) (m : X → ι → ℂ) (m₀ : ι → ℂ)
    (l : X → ι → ℝ) (l₀ : ι → ℝ)
    (hm : Tendsto m L (𝓝 m₀)) (hl : Tendsto l L (𝓝 l₀))
    (hreal : ∀ i, (m₀ i).im=0) (hnz : ∀ i, m₀ i≠0) :
    Tendsto (fun x => perronDensity (l x) (m x)) L (𝓝 0) := by
  have h : Tendsto (fun x => ∑ i, l x i*normalizedImag (m x) i) L
      (𝓝 (∑ i, l₀ i*0)) := tendsto_finset_sum _ (fun i _ =>
        ((continuous_apply i).continuousAt.tendsto.comp hl).mul
          (normalizedImag_tendsto_zero L m m₀ hm hreal hnz i))
  simpa [perronDensity] using h

/-- Complete uniform spectral Taylor conclusion along a genuine varying
Perron frame. Its hypotheses are actual equation/limit/frame facts, not a
spectral conclusion for the Dyson phase. -/
theorem varying_spectral_expansion {X : Type*} {n : ℕ} (hn : 0<n)
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (L : Filter X) (z : X → ℂ) (m : X → Fin n → ℂ) (m₀ : Fin n → ℂ)
    (frame : VaryingFrame S m L m₀)
    (hm : Tendsto m L (𝓝 m₀)) (hη : Tendsto (fun x => (z x).im) L (𝓝 0))
    (hreal : ∀ i, (m₀ i).im=0) (hnz : ∀ i, m₀ i≠0)
    (p : Fin n → ℝ) (hp : ∀ i, p i^2=1) (hp0 : ∀ i, 0<p i*(m₀ i).re)
    (hactual : ∀ᶠ x in L, (∀ i, m x i≠0) ∧ BasicEstimates.IsDysonSolution S a (z x) (m x) ∧
      (∀ i, 0 ≤ normalizedImag (m x) i) ∧ 0 ≤ (z x).im) :
    ∃ ρ C : ℝ, 0<ρ ∧ 0<C ∧ ∀ᶠ x in L,
      ∃ (u : Fin n → ℝ) (d : SimpleSpectralSplit (reducedOperator S (m x))),
        frame.K x (fun i => (p i:ℂ)*(frame.r x i:ℂ)^2)=(fun i => (u i:ℂ)) ∧
        HasDysonSpectralEstimates S (m x) p (frame.r x) (frame.l x) u (frame.K x)
          (frame.lam x) (perronDensity (frame.l x) (m x)) (z x).im ρ C d := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨B,b,hB,hb,hbounds⟩ := frame.uniform
  obtain ⟨ε,ρ,C,hε,hε1,hρ,hC,ht⟩ := dyson_spectral_expansion_uniform external B b hB hb
  have hδlim := perronDensity_tendsto_zero L m m₀ frame.l frame.l₀ hm frame.left_limit hreal hnz
  have hδsmall : ∀ᶠ x in L, perronDensity (frame.l x) (m x) ≤ ε :=
    hδlim.eventually_le_const hε
  have hηsmall : ∀ᶠ x in L, (z x).im ≤ ε := hη.eventually_le_const hε
  have hlamlim : Tendsto (fun x => |1-frame.lam x|) L (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : X => (1:ℝ)) L (𝓝 1)).sub frame.lam_limit).abs
  have hlamsmall : ∀ᶠ x in L, |1-frame.lam x| ≤ ε :=
    hlamlim.eventually_le_const hε
  have hsign : ∀ᶠ x in L, ∀ i, 0 ≤ p i*(m x i).re := by
    apply Filter.eventually_all.mpr
    intro i
    exact (PhaseTaylor.eventually_real_sign (fun x => m x i) (m₀ i) (p i)
      ((continuous_apply i).continuousAt.tendsto.comp hm) (hp0 i)).mono (fun _ h => h.le)
  refine ⟨ρ,C,hρ,hC,?_⟩
  filter_upwards [hbounds,frame.nearby,frame.restricted,frame.real_preserving,
    hδsmall,hηsmall,hlamsmall,hsign,hactual] with x hbds hd hK hr hδ hηb hlamb hs hx
  obtain ⟨hrb,hlb,hKb,hqb,_,hlow⟩ := hbds
  obtain ⟨hmx,heq,hv,hη0⟩ := hx
  exact ht S a (z x) (m x) p (frame.r x) (frame.l x) (frame.K x) (frame.lam x)
    hmx heq hv hp hs hrb hlb hKb hqb hlow hd.normalized hd.right_eigen hd.left_eigen
    hK hr hδ hη0 hηb hlamb

/-- The phase expansion on the same full approach domain is proved directly
from the actual normalized imaginary equation, independently of spectral
perturbation. -/
theorem varying_phase_expansion {X : Type*} {n : ℕ} (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (L : Filter X) (z : X → ℂ) (m : X → Fin n → ℂ) (m₀ : Fin n → ℂ)
    (frame : VaryingFrame S m L m₀)
    (hm : Tendsto m L (𝓝 m₀)) (hη : Tendsto (fun x => (z x).im) L (𝓝 0))
    (hreal : ∀ i, (m₀ i).im=0) (hnz : ∀ i, m₀ i≠0)
    (p : Fin n → ℝ) (hp : ∀ i, p i^2=1) (hp0 : ∀ i, 0<p i*(m₀ i).re)
    (hactual : ∀ᶠ x in L, (∀ i, m x i≠0) ∧ BasicEstimates.IsDysonSolution S a (z x) (m x) ∧
      (∀ i, 0 ≤ normalizedImag (m x) i) ∧ 0 ≤ (z x).im) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x in L,
      ‖phaseOperator (m x)-ContinuousLinearMap.id ℂ (Vec (Fin n)) -
        (perronDensity (frame.l x) (m x):ℂ) • firstPhase p (frame.r x) -
        ((perronDensity (frame.l x) (m x):ℂ)^2) • secondPhase (frame.r x)‖ ≤
      C*((perronDensity (frame.l x) (m x))^3+(z x).im) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨B,b,hB,hb,hbounds⟩ := frame.uniform
  have hδlim := perronDensity_tendsto_zero L m m₀ frame.l frame.l₀ hm frame.left_limit hreal hnz
  have hδsmall : ∀ᶠ x in L, perronDensity (frame.l x) (m x) ≤ 1 :=
    hδlim.eventually_le_const (by norm_num)
  have hηsmall : ∀ᶠ x in L, (z x).im ≤ 1 := hη.eventually_le_const (by norm_num)
  have hsign : ∀ᶠ x in L, ∀ i, 0 ≤ p i*(m x i).re := by
    apply Filter.eventually_all.mpr
    intro i
    exact (PhaseTaylor.eventually_real_sign (fun x => m x i) (m₀ i) (p i)
      ((continuous_apply i).continuousAt.tendsto.comp hm) (hp0 i)).mono (fun _ h => h.le)
  refine ⟨1+8*(B^3+B^3)+2*B*(2+B),by positivity,?_⟩
  filter_upwards [hbounds,frame.restricted,frame.real_preserving,frame.nearby,
    hδsmall,hηsmall,hsign,hactual] with x hbds hK hr hd hδ hηb hs hx
  obtain ⟨hrb,hlb,hKb,hqb,hKqb,hlow⟩ := hbds
  obtain ⟨hmx,heq,hv,hη0⟩ := hx
  obtain ⟨t,ht⟩ := hr (fun i => ‖m x i‖)
  have hri : ∀ i, |frame.r x i|≤B := fun i => by
    simpa using (norm_le_pi_norm (fun j => (frame.r x j:ℂ)) i).trans hrb
  have hti : ∀ i, |t i|≤B := fun i => by
    have hh := (norm_le_pi_norm (frame.K x (fun j => (‖m x j‖:ℂ))) i).trans hKqb
    simpa [ht] using hh
  exact phase_operator_taylor (m x) hmx p (frame.r x) t _ _ B B hp hs
    (perron_density_nonneg _ _ (fun i => (hd.left_positive i).le) hv) hδ hη0 hηb hB.le hB.le
    hri hti (imaginary_direction_real S a (z x) (m x) hmx heq (frame.r x) (frame.l x) t (frame.K x) hK ht)

end NonSymmetricDyson.Full.SingularSpectral
