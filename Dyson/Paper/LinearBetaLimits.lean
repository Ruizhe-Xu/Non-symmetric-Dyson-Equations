import Dyson.Paper.LinearEdgeBeta

noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.LinearBeta
variable {X : Type*} {L : Filter X}

/-- Uniform neighborhood form of the original spectral absorption. -/
theorem beta_lower_eventually (β : X → ℂ) (a σ ψ δ η μ : X → ℝ)
    {c C b : ℝ} (hc : 0<c) (hC : 0≤C) (hb : 0<b)
    (hδlim : Tendsto δ L (𝓝 0)) (hσδ : Tendsto (fun x => |σ x| * δ x) L (𝓝 0))
    (hdata : ∀ᶠ x in L,0≤a x ∧ 0≤δ x ∧ 0≤η x ∧ 0≤ψ x ∧ c≤μ x ∧
      μ x*η x=a x*δ x ∧ b≤(σ x)^2+ψ x ∧
      ‖β x-model (a x) (σ x) (ψ x) (δ x)‖≤C*((δ x)^3+η x)) :
    ∀ᶠ x in L,(min 1 b/8)*(a x+(δ x)^2)≤‖β x‖ := by
  have hs := hσδ.eventually_le_const (by norm_num : (0:ℝ)<1)
  have ht : Tendsto (fun x => C*(1+c⁻¹)*δ x) L (𝓝 0) := by
    simpa using hδlim.const_mul (C*(1+c⁻¹))
  have he : ∀ᶠ x in L,C*(1+c⁻¹)*δ x≤ min 1 b/8 :=
    ht.eventually_le_const (by positivity)
  filter_upwards [hdata,hs,he] with x hx hσx hδx
  exact beta_lower_from_original_expansion hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hc
    hx.2.2.2.2.1 hx.2.2.2.2.2.1 hC hb hx.2.2.2.2.2.2.1 hσx hδx hx.2.2.2.2.2.2.2

/-- On an edge the nonzero quadratic coefficient persists; the same
uniform neighborhood works on the support and gap sides. -/
theorem edge_beta_eventually (β : X → ℂ) (a σ ψ δ η μ : X → ℝ)
    {c C D s M : ℝ} (hc : 0<c) (hC : 0≤C) (hD : 0≤D) (hs : 0<s) (hM : 0≤M)
    (hδlim : Tendsto δ L (𝓝 0))
    (hdata : ∀ᶠ x in L,0≤a x ∧ 0≤δ x ∧ 0≤η x ∧ c≤μ x ∧
      μ x*η x=a x*δ x ∧ s≤|σ x| ∧ |σ x|≤M ∧ |ψ x-(σ x)^2|≤D ∧
      ‖β x-model (a x) (σ x) (ψ x) (δ x)‖≤C*((δ x)^3+η x)) :
    ∀ᶠ x in L,(min 1 (2*s)/4)*(a x+δ x)≤‖β x‖ ∧
      ‖β x‖≤(1+2*M+min 1 (2*s)/4)*(a x+δ x) := by
  have h1 := hδlim.eventually_le_const (by norm_num : (0:ℝ)<1)
  have ht : Tendsto (fun x => (2*D+C*(1+c⁻¹))*δ x) L (𝓝 0) := by
    simpa using hδlim.const_mul (2*D+C*(1+c⁻¹))
  have he : ∀ᶠ x in L,(2*D+C*(1+c⁻¹))*δ x≤ min 1 (2*s)/4 :=
    ht.eventually_le_const (by positivity)
  filter_upwards [hdata,h1,he] with x hx hδ1 hsmall
  obtain ⟨ha,hδ,hη,hμ,hid,hσlo,hσhi,hquad,herr⟩ := hx
  have hrem := edge_remainder_absorption ha hδ hδ1 hη hc hμ hid hC hD hquad hsmall herr
  exact ⟨edge_beta_lower ha hδ hs hσlo hrem,edge_beta_upper ha hδ hM hσhi hrem⟩

end NonSymmetricDyson.Paper.LinearBeta
