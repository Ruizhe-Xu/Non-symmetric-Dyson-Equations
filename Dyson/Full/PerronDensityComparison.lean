import Dyson.Full.PerronVarying
import Dyson.Full.SpectralPhase

/-! Quantitative comparison between the Perron density parameter and the
actual sum of component densities, uniformly near a regular boundary point. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.PerronContinuation
open SingularSpectral
variable {X : Type*} {n : ℕ} [Nonempty (Fin n)]

theorem positive_component_lower_bound {L : Filter X} (m : X → Fin n → ℂ)
    (m₀ : Fin n → ℂ) (hm : Tendsto m L (𝓝 m₀)) (hnz : ∀ i,m₀ i≠0) :
    ∃ q : ℝ,0<q ∧ ∀ᶠ x in L,∀ i,q≤‖m x i‖ := by
  classical
  let q : ℝ := (Finset.univ.inf' Finset.univ_nonempty (fun i => ‖m₀ i‖))/2
  have hq : 0<q := half_pos ((Finset.lt_inf'_iff _).mpr
    (fun i _ => norm_pos_iff.mpr (hnz i)))
  refine ⟨q,hq,Filter.eventually_all.mpr ?_⟩
  intro i
  apply ((tendsto_pi_nhds.mp hm) i).norm.eventually_const_le
  have hh := Finset.inf'_le (fun i => ‖m₀ i‖) (Finset.mem_univ i)
  dsimp [q]
  linarith [norm_pos_iff.mpr (hnz i)]

theorem perron_density_comparison (m : Fin n → ℂ) (l : Fin n → ℝ)
    (b B q Q : ℝ) (hb : 0<b) (hB : 0<B) (hq : 0<q) (hQ : 0<Q)
    (hl : ∀ i,b≤l i ∧ l i≤B) (hm : ∀ i,q≤‖m i‖ ∧ ‖m i‖≤Q)
    (him : ∀ i,0≤(m i).im) :
    (b/Q)*(∑ i,(m i).im)≤perronDensity l m ∧
      perronDensity l m≤(B/q)*(∑ i,(m i).im) := by
  have hlo (i : Fin n) : b/Q≤l i/‖m i‖ :=
    (div_le_div_of_nonneg_left hb.le (hq.trans_le (hm i).1) (hm i).2).trans
      (div_le_div_of_nonneg_right (hl i).1 (norm_nonneg _))
  have hhi (i : Fin n) : l i/‖m i‖≤B/q :=
    (div_le_div_of_nonneg_right (hl i).2 (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hB.le hq (hm i).1)
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    convert mul_le_mul_of_nonneg_right (hlo i) (him i) using 1 <;>
      dsimp [normalizedImag] <;> ring
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    convert mul_le_mul_of_nonneg_right (hhi i) (him i) using 1 <;>
      dsimp [normalizedImag] <;> ring

/-- Uniform δ≍sum Im m_i follows from actual component limits and the moving
Perron frame. It holds wherever the component imaginary parts are nonnegative. -/
theorem VaryingFrame.density_comparison {S : Matrix (Fin n) (Fin n) ℝ}
    {m : X → Fin n → ℂ} {L : Filter X} {m₀ : Fin n → ℂ}
    (d : VaryingFrame S m L m₀) (hm : Tendsto m L (𝓝 m₀)) (hnz : ∀ i,m₀ i≠0) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ x in L,(∀ i,0≤(m x i).im) →
      c*(∑ i,(m x i).im)≤perronDensity (d.l x) (m x) ∧
      perronDensity (d.l x) (m x)≤C*(∑ i,(m x i).im) := by
  obtain ⟨B,b,hB,hb,hbds⟩ := d.uniform
  obtain ⟨q,hq,hqlow⟩ := positive_component_lower_bound m m₀ hm hnz
  let P : ℝ := ‖d.l₀‖+1
  let Q : ℝ := ‖m₀‖+1
  have hP : 0<P := by dsimp [P]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hl : ∀ᶠ x in L, ‖d.l x‖≤P := d.left_limit.norm.eventually_le_const
    (by dsimp [P]; linarith)
  have hmQ : ∀ᶠ x in L, ‖m x‖≤Q := hm.norm.eventually_le_const (by dsimp [Q]; linarith)
  refine ⟨b/Q,P/q,div_pos hb hQ,div_pos hP hq,?_⟩
  filter_upwards [hbds,hqlow,hl,hmQ] with x hbx hqx hlx hmx
  intro him
  apply perron_density_comparison (m x) (d.l x) b P q Q hb hP hq hQ
  · intro i
    refine ⟨hbx.2.2.2.2.2 i,?_⟩
    exact (le_abs_self _).trans ((norm_le_pi_norm (d.l x) i).trans hlx)
  · exact fun i => ⟨hqx i,(norm_le_pi_norm (m x) i).trans hmx⟩
  · exact him

end NonSymmetricDyson.Full.PerronContinuation
