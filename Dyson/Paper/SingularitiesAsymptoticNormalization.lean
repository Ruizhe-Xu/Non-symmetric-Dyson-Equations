import Dyson.Full.MainSingularityEndpoints

/-! Conversion from the monomial radius to the literal powers and one-sided
sign convention appearing in the revised fifth theorem. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Paper.SingularitiesAsymptoticNormalization
open Full.Singularities
variable {ι : Type*}

theorem edge_power_form (v : ι → ℝ → ℝ) (τ c C : ℝ) (D : ι → ℝ)
    (hc : c≠0) (hD : ∀ i,0<D i) (hC : 0<C)
    (hloc : ∀ᶠ x in 𝓝 τ, ∀ i,
      (c*(x-τ)<0 → |v i x-D i*rootRadius c 2 (x-τ)| ≤ C*(rootRadius c 2 (x-τ))^2) ∧
      (0<c*(x-τ) → v i x=0)) :
    ∃ (s : ℝ) (d : ι → ℝ) (B : ℝ), (s=1 ∨ s= -1) ∧ (∀ i,0<d i) ∧ 0<B ∧
      ∀ᶠ ω in 𝓝[Set.Ioi 0] 0, ∀ i,
        |v i (τ+s*ω)-d i*Real.sqrt ω| ≤ B*ω ∧ v i (τ-s*ω)=0 := by
  have hs : ∃ s:ℝ,(s=1 ∨ s= -1) ∧ c*s<0 ∧ |s|=1 := by
    rcases lt_or_gt_of_ne hc with hn|hp
    · exact ⟨1,Or.inl rfl,by simpa using hn,by norm_num⟩
    · exact ⟨-1,Or.inr rfl,by nlinarith,by norm_num⟩
  obtain ⟨s,hs,hcs,habss⟩ := hs
  have ha : 0 < |c| := abs_pos.mpr hc
  have hsq : 0<Real.sqrt |c| := Real.sqrt_pos.mpr ha
  refine ⟨s,fun i => D i/Real.sqrt |c|,C/|c|,hs,
    fun i => div_pos (hD i) hsq,div_pos hC ha,?_⟩
  have hplus : Tendsto (fun ω:ℝ => τ+s*ω) (𝓝[Set.Ioi 0] 0) (𝓝 τ) := by
    have ht : Tendsto (fun ω:ℝ => τ+s*ω) (𝓝 0) (𝓝 (τ+s*0)) :=
      (by fun_prop : Continuous (fun ω:ℝ => τ+s*ω)).tendsto 0
    simpa using ht.mono_left nhdsWithin_le_nhds
  have hminus : Tendsto (fun ω:ℝ => τ-s*ω) (𝓝[Set.Ioi 0] 0) (𝓝 τ) := by
    have ht : Tendsto (fun ω:ℝ => τ-s*ω) (𝓝 0) (𝓝 (τ-s*0)) :=
      (by fun_prop : Continuous (fun ω:ℝ => τ-s*ω)).tendsto 0
    simpa using ht.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hplus.eventually hloc,hminus.eventually hloc] with ω hω hp hm i
  have hcp : c*(τ+s*ω-τ)<0 := by
    have hh := mul_neg_of_neg_of_pos hcs hω
    nlinarith
  have hcm : 0<c*(τ-s*ω-τ) := by
    have hh := mul_neg_of_neg_of_pos hcs hω
    nlinarith
  have hr : rootRadius c 2 (τ+s*ω-τ)=Real.sqrt ω/Real.sqrt |c| := by
    have he : |τ+s*ω-τ|=ω := by
      rw [add_sub_cancel_left,abs_mul,habss,one_mul,abs_of_pos hω]
    rw [rootRadius,he]
    norm_num only [Nat.cast_ofNat,inv_eq_one_div]
    rw [← Real.sqrt_eq_rpow,Real.sqrt_div hω.le]
  refine ⟨?_,(hm i).2 hcm⟩
  have hh := (hp i).1 hcp
  rw [hr] at hh
  have he : D i*(Real.sqrt ω/Real.sqrt |c|)=(D i/Real.sqrt |c|)*Real.sqrt ω := by ring
  have he2 : C*(Real.sqrt ω/Real.sqrt |c|)^2=(C/|c|)*ω := by
    rw [div_pow,Real.sq_sqrt hω.le,Real.sq_sqrt ha.le]
    ring
  rwa [he,he2] at hh

theorem cusp_power_form (v : ι → ℝ → ℝ) (τ c C : ℝ) (D : ι → ℝ)
    (hc : c≠0) (hD : ∀ i,0<D i) (hC : 0<C)
    (hloc : ∀ᶠ x in 𝓝 τ, ∀ i,
      |v i x-D i*rootRadius c 3 (x-τ)| ≤ C*(rootRadius c 3 (x-τ))^2) :
    ∃ (d : ι → ℝ) (B : ℝ), (∀ i,0<d i) ∧ 0<B ∧
      ∀ᶠ ω:ℝ in 𝓝 0, ∀ i,
        |v i (τ+ω)-d i*|ω|^((1:ℝ)/3)| ≤ B*|ω|^((2:ℝ)/3) := by
  have ha : 0 < |c| := abs_pos.mpr hc
  let R : ℝ := |c|^((1:ℝ)/3)
  have hR : 0<R := Real.rpow_pos_of_pos ha _
  refine ⟨fun i => D i/R,C/R^2,fun i => div_pos (hD i) hR,
    div_pos hC (sq_pos_of_pos hR),?_⟩
  have ht : Tendsto (fun ω:ℝ => τ+ω) (𝓝 0) (𝓝 τ) := by
    simpa using (continuous_const.add continuous_id).tendsto (0:ℝ)
  filter_upwards [ht.eventually hloc] with ω hω i
  have hr : rootRadius c 3 (τ+ω-τ)=|ω|^((1:ℝ)/3)/R := by
    rw [rootRadius,add_sub_cancel_left,Real.div_rpow (abs_nonneg _) (abs_nonneg _)]
    norm_num [R,inv_eq_one_div]
  have hh := hω i
  rw [hr] at hh
  have he : D i*(|ω|^((1:ℝ)/3)/R)=(D i/R)*|ω|^((1:ℝ)/3) := by ring
  have he2 : C*(|ω|^((1:ℝ)/3)/R)^2=(C/R^2)*|ω|^((2:ℝ)/3) := by
    rw [div_pow,← Real.rpow_mul_natCast (abs_nonneg ω)]
    norm_num
    ring
  rwa [he,he2] at hh

end NonSymmetricDyson.Paper.SingularitiesAsymptoticNormalization
