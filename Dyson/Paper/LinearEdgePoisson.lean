import Dyson.Paper.SingularityPoissonModel

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearEdgePoisson
open Full Full.ExternalAlgebraic SingularityPoissonOrientation

/-- The common physical orientation is retained when summing all components. -/
theorem sum_profiles {n : ℕ} (hn : 0<n) (m : ℂ → Fin n → ℂ) (τ : ℝ) (left : Bool)
    (profiles : ∀ j,∃ cs Cs cg Cg ε : ℝ,
      0<cs ∧ 0<Cs ∧ 0<cg ∧ 0<Cg ∧ 0<ε ∧
      ∀ κ η : ℝ,0≤κ → 0<η → κ+η<ε →
        (cs*Real.sqrt (κ+η) ≤ (m (Poisson.point (τ+direction left*κ) η) j).im ∧
          (m (Poisson.point (τ+direction left*κ) η) j).im ≤ Cs*Real.sqrt (κ+η)) ∧
        (cg*(η/Real.sqrt (κ+η)) ≤ (m (Poisson.point (τ-direction left*κ) η) j).im ∧
          (m (Poisson.point (τ-direction left*κ) η) j).im ≤ Cg*(η/Real.sqrt (κ+η)))) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),
      if 0≤direction left*(z.re-τ) then
        c*Real.sqrt (|z.re-τ|+z.im)≤∑j,(m z j).im ∧
          (∑j,(m z j).im)≤C*Real.sqrt (|z.re-τ|+z.im)
      else
        c*z.im≤(∑j,(m z j).im)*Real.sqrt (|z.re-τ|+z.im) ∧
          (∑j,(m z j).im)*Real.sqrt (|z.re-τ|+z.im)≤C*z.im := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  choose cs Cs cg Cg ε hcs hCs hcg hCg hε hp using profiles
  let c : ℝ := ∑j,min (cs j) (cg j)
  let C : ℝ := ∑j,max (Cs j) (Cg j)
  have hc : 0<c := Finset.sum_pos (fun j _ => lt_min (hcs j) (hcg j)) Finset.univ_nonempty
  have hC : 0<C := Finset.sum_pos (fun j _ => (hCs j).trans_le (le_max_left _ _)) Finset.univ_nonempty
  have hq : Tendsto (fun z:ℂ => |z.re-τ|+z.im) (𝓝[upper] (τ:ℂ)) (𝓝 0) := by
    have hh : Continuous (fun z:ℂ => |z.re-τ|+z.im) :=
      ((Complex.continuous_re.sub continuous_const).abs).add Complex.continuous_im
    simpa using hh.continuousAt.tendsto.mono_left (show 𝓝[upper] (τ:ℂ)≤𝓝 (τ:ℂ) from nhdsWithin_le_nhds)
  have he : ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀j,|z.re-τ|+z.im<ε j :=
    Filter.eventually_all.mpr (fun j => hq.eventually_lt_const (hε j))
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [he,self_mem_nhdsWithin] with z he hz
  have ht : 0<Real.sqrt (|z.re-τ|+z.im) := Real.sqrt_pos.mpr (by positivity)
  have hsquare : (direction left)^2=1 := by cases left <;> norm_num [direction]
  by_cases hside : 0≤direction left*(z.re-τ)
  · rw [if_pos hside]
    have heq : τ+direction left*|z.re-τ|=z.re := by
      cases left <;> simp only [direction,Bool.false_eq_true,↓reduceIte] at hside ⊢
      · rw [abs_of_nonpos (by linarith : z.re-τ≤0)]; ring
      · rw [abs_of_nonneg (by linarith : 0≤z.re-τ)]; ring
    have hpoint : Poisson.point (τ+direction left*|z.re-τ|) z.im=z := by
      rw [heq]; apply Complex.ext <;> simp [Poisson.point]
    have hb (j : Fin n) := (hp j |z.re-τ| z.im (abs_nonneg _) hz (he j)).1
    simp only [hpoint] at hb
    constructor
    · calc
        c*Real.sqrt (|z.re-τ|+z.im)=∑j,min (cs j) (cg j)*Real.sqrt (|z.re-τ|+z.im) := by simp [c,Finset.sum_mul]
        _ ≤ ∑j,(m z j).im := Finset.sum_le_sum (fun j _ =>
          (mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le).trans (hb j).1)
    · calc
        (∑j,(m z j).im)≤∑j,max (Cs j) (Cg j)*Real.sqrt (|z.re-τ|+z.im) := Finset.sum_le_sum (fun j _ =>
          (hb j).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le))
        _ = C*Real.sqrt (|z.re-τ|+z.im) := by simp [C,Finset.sum_mul]
  · rw [if_neg hside]
    have heq : τ-direction left*|z.re-τ|=z.re := by
      cases left <;> simp only [direction,Bool.false_eq_true,↓reduceIte] at hside ⊢
      · rw [abs_of_nonneg (by linarith : 0≤z.re-τ)]; ring
      · rw [abs_of_nonpos (by linarith : z.re-τ≤0)]; ring
    have hpoint : Poisson.point (τ-direction left*|z.re-τ|) z.im=z := by
      rw [heq]; apply Complex.ext <;> simp [Poisson.point]
    have hb (j : Fin n) := (hp j |z.re-τ| z.im (abs_nonneg _) hz (he j)).2
    simp only [hpoint] at hb
    have hlo (j : Fin n) : min (cs j) (cg j)*z.im≤(m z j).im*Real.sqrt (|z.re-τ|+z.im) := by
      have hh := mul_le_mul_of_nonneg_right (hb j).1 ht.le
      have hcj := mul_le_mul_of_nonneg_right (min_le_right (cs j) (cg j)) hz.le
      field_simp at hh
      exact hcj.trans (by simpa [mul_comm] using hh)
    have hhi (j : Fin n) : (m z j).im*Real.sqrt (|z.re-τ|+z.im)≤ max (Cs j) (Cg j)*z.im := by
      have hh := mul_le_mul_of_nonneg_right (hb j).2 ht.le
      have hcj := mul_le_mul_of_nonneg_right (le_max_right (Cs j) (Cg j)) hz.le
      field_simp at hh
      exact (show (m z j).im*Real.sqrt (|z.re-τ|+z.im)≤Cg j*z.im by simpa [mul_comm] using hh).trans hcj
    constructor
    · simpa [c,Finset.sum_mul] using Finset.sum_le_sum (fun j (_:j∈Finset.univ) => hlo j)
    · simpa [C,Finset.sum_mul] using Finset.sum_le_sum (fun j (_:j∈Finset.univ) => hhi j)

end NonSymmetricDyson.Paper.LinearEdgePoisson
