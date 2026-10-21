import Dyson.Paper.SingularitiesNB
import Dyson.Full.BoundaryLocalLimits
import Dyson.Full.CubicUniform

/-! Original Sym/NB nondegeneracy through Jensen equality and the exceptional
constant-potential reflection argument. No Möbius-family theorem is used. -/
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NonSymmetricDyson.Paper.SingularitiesNondegenerate
open Full.Singularities SingularitiesJensen
variable {ι : Type*} [Fintype ι]

/-- The paper's uniqueness/reflection exclusion of the exceptional point.
The limits and the equations are the actual physical ones. -/
theorem constant_potential_limit_impossible
    (S : ι → ι → ℝ) (a : ι → ℝ) (τ : ℝ)
    (m : ℝ → ι → ℂ) (m₀ : ι → ℂ)
    (hS : ∀ i j,0 ≤ S i j) (ha : ∀ i,a i=τ)
    (hm : ∀ η,0 < η → BasicEstimates.IsUpperSolution (m η))
    (heq : ∀ η : ℝ,0 < η → BasicEstimates.IsDysonSolution S a
      ((τ : ℂ)+(η : ℂ)*Complex.I) (m η))
    (hlim : Tendsto m (𝓝[Set.Ioi 0] 0) (𝓝 m₀))
    (hreal : ∀ i,(m₀ i).im=0) (i : ι) (hne : m₀ i≠0) : False := by
  have heq0 : ∀ η : ℝ,0 < η → BasicEstimates.IsDysonSolution S (fun _ => 0)
      ((η : ℂ)*Complex.I) (m η) := by
    intro η hη j
    have hh := heq η hη j
    simpa [ha j,add_sub_cancel_left] using hh
  have hh := Full.Origin.imaginary_boundary_of_limit S m m₀ hS hm heq0 hlim
  have hz := congrFun hh i
  simp [Full.BulkOriginData.imaginaryVector,hreal] at hz
  exact hne hz

/-- Real scalar data for the symmetric equality argument. The only possible
Jensen equality mode forces a constant potential, excluded by `hnot`.
`hnot` will be proved from the physical limit in the actual-frontier wrapper. -/
theorem symmetric_positive
    (S : ι → ι → ℝ) (a m p q r l u : ι → ℝ) (τ : ℝ)
    (hS : ∀ i j,0 ≤ S i j) (hsym : ∀ i j,S i j=S j i)
    (hp : ∀ i,p i^2=1) (hq : ∀ i,0 < q i)
    (hr : ∀ i,0 < r i) (hl : ∀ i,0 < l i)
    (hm : ∀ i,m i=p i*q i)
    (hFr : ∀ i,∑ j,(q i*S i j*q j)*r j=r i)
    (hlF : ∀ j,∑ i,l i*(q i*S i j*q j)=l j)
    (hu : ∀ i,u i-∑ j,(q i*S i j*q j)*u j=p i*r i^2)
    (hsol : ∀ i,-(m i)⁻¹=τ-a i+∑ j,S i j*m j)
    (hnot : ¬∀ i,a i=τ) :
    0 < cubicCoefficient (fun i j => q i*S i j*q j) p l r u := by
  let F : ι → ι → ℝ := fun i j => q i*S i j*q j
  have hF : ∀ i j,0 ≤ F i j := fun i j =>
    mul_nonneg (mul_nonneg (hq i).le (hS i j)) (hq j).le
  have hn := cubicCoefficient_nonnegative F p l r u hF hl hr hFr hlF hu
  by_contra hpos
  have hz : cubicCoefficient F p l r u=0 := le_antisymm (le_of_not_gt hpos) hn
  have he := zero_cubic_edge_difference F p l r u hF hl hr hFr hlF hu hz
  have hc : ∀ i j,0 < S i j → u i/r i-u j/r j=p i*r i := by
    intro i j hij
    exact he i j (mul_pos (mul_pos (hq i) hij) (hq j))
  have halt := symmetric_coboundary_alternates (fun i j => 0 < S i j)
    (fun i j hij => by change 0 < S j i; rw [hsym j i];exact hij) (fun i => u i/r i)
    (fun i => p i*r i) hc
  exact hnot (alternating_perron_forces_constant_potential S a m p q r τ hS hp hq hr hm hFr hsol halt)

section NB
open Nonbacktracking Full.BulkGraph
variable {V : Type*} [Fintype V] (G : BaseGraph V)

/-- Exact conversion of the positive Perron equation to the signed real
NB equation after writing m=pq and h=pr. -/
theorem signed_perron (m p q r : G.Edge → ℝ)
    (hp : ∀ e,p e^2=1) (hm : ∀ e,m e=p e*q e)
    (hf : ∀ e,∑ f,(q e*G.matrix e f*q f)*r f=r e) :
    ∀ e,p e*r e=m e*(∑ f,G.matrix e f*m f*(p f*r f)) := by
  intro e
  rw [hm,Finset.mul_sum]
  calc
    _ = p e*(∑ f,(q e*G.matrix e f*q f)*r f) := by rw [hf]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [hm]
      have hh := hp f
      calc
        _ = p e*q e*G.matrix e f*q f*r f*1 := by ring
        _ = p e*q e*G.matrix e f*q f*r f*(p f^2) := by rw [hh]
        _ = _ := by ring

theorem nb_positive (deg : NB.HasThreeNeighbors G)
    (a : V → ℝ) (τ : ℝ) (m p q r l u : G.Edge → ℝ)
    (hp : ∀ e,p e^2=1) (hq : ∀ e,0 < q e)
    (hr : ∀ e,0 < r e) (hl : ∀ e,0 < l e)
    (hm : ∀ e,m e=p e*q e)
    (hFr : ∀ e,∑ f,(q e*G.matrix e f*q f)*r f=r e)
    (hlF : ∀ f,∑ e,l e*(q e*G.matrix e f*q f)=l f)
    (hu : ∀ e,u e-∑ f,(q e*G.matrix e f*q f)*u f=p e*r e^2)
    (hsol : ∀ e,-(m e)⁻¹=τ-a (G.head e)+∑ f,G.matrix e f*m f)
    (hnot : ¬∀ e:G.Edge,a (G.head e)=τ) :
    0 < cubicCoefficient (fun e f => q e*G.matrix e f*q f) p l r u := by
  let F : G.Edge → G.Edge → ℝ := fun e f => q e*G.matrix e f*q f
  have hF : ∀ e f,0 ≤ F e f := fun e f =>
    mul_nonneg (mul_nonneg (hq e).le (G.matrix_nonnegative e f)) (hq f).le
  have hn := cubicCoefficient_nonnegative F p l r u hF hl hr hFr hlF hu
  by_contra hpos
  have hz : cubicCoefficient F p l r u=0 := le_antisymm (le_of_not_gt hpos) hn
  let y : G.Edge → ℝ := fun e => u e/r e
  let c : G.Edge → ℝ := fun e => (∑ f,F e f*u f)/r e
  have he := cubicCoefficient_zero_edge F p l r u hF hl hr hFr hlF hu hz
  have hed : ∀ e f,G.CanFollow e f → y f=c e := by
    intro e f hef
    apply he e f
    dsimp [F]
    simp only [BaseGraph.matrix,if_pos hef,mul_one]
    exact mul_pos (hq e) (hq f)
  obtain ⟨φ,hφ⟩ := SingularitiesNB.equality_space G deg y c hed
  have hd : ∀ e,p e*r e=φ (G.tail e)-φ (G.head e) := by
    intro e
    rw [← (hφ e).1,← (hφ e).2]
    dsimp [y,c]
    rw [← sub_div,hu]
    field_simp [(hr e).ne']
  have hp0 (e : G.Edge) : p e≠0 := by
    intro hz
    have hh := hp e
    simp [hz] at hh
  have hm0 (e : G.Edge) : m e≠0 := by rw [hm];exact mul_ne_zero (hp0 e) (hq e).ne'
  have hpr0 (e : G.Edge) : p e*r e≠0 := mul_ne_zero (hp0 e) (hr e).ne'
  have hprod (e : G.Edge) : 0 < m e*(p e*r e) := by
    rw [hm]
    have hh : (p e*q e)*(p e*r e)=q e*r e := by
      calc
        _ = p e^2*(q e*r e) := by ring
        _ = _ := by rw [hp,one_mul]
    rw [hh]
    exact mul_pos (hq e) (hr e)
  have hpf := signed_perron G m p q r hp hm hFr
  have halt := SingularitiesNB.terminal_equations_force_alternation G a τ m
    (fun e => p e*r e) φ hm0 hprod hd hpf hsol
  exact hnot (SingularitiesNB.alternating_forces_terminal_potential G a τ m
    (fun e => p e*r e) hm0 hpr0 hpf hsol halt)
end NB
end NonSymmetricDyson.Paper.SingularitiesNondegenerate
