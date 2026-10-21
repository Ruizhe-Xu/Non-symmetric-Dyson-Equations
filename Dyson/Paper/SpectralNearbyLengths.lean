import Dyson.Paper.SpectralLengths

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Spectral Full.Singularities Full.SingularSpectral Full.PerronContinuation

/-- Component and pairing bounds for every split satisfying the actual
Taylor estimates, uniformly along the same varying Perron frame. -/
theorem varying_spectral_lengths {X : Type*} {n : ℕ} (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ) (m : X → Fin n → ℂ) (L : Filter X) (m₀ : Fin n → ℂ)
    (frame : VaryingFrame S m L m₀) (hm : Tendsto m L (𝓝 m₀))
    (eta : X → ℝ) (hη : Tendsto eta L (𝓝 0))
    (hreal : ∀ i,(m₀ i).im=0) (hnz : ∀ i,m₀ i≠0)
    (p : Fin n → ℝ) (rho C : ℝ) :
    ∃ b B : ℝ,0<b ∧ 0<B ∧ ∀ᶠ x in L,
      ∀ (u : Fin n → ℝ) (d : SimpleSpectralSplit (reducedOperator S (m x))),
      HasDysonSpectralEstimates S (m x) p (frame.r x) (frame.l x) u (frame.K x)
        (frame.lam x) (perronDensity (frame.l x) (m x)) (eta x) rho C d →
      (∀ i,b≤‖d.right i‖ ∧ ‖d.right i‖≤B) ∧
      (∀ i,b≤‖leftCoefficient d.left i‖ ∧ ‖leftCoefficient d.left i‖≤B) ∧
      b≤‖d.left d.right‖ ∧ ‖d.left d.right‖≤B := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let delta := fun x => perronDensity (frame.l x) (m x)
  have hd : Tendsto delta L (𝓝 0) := perronDensity_tendsto_zero L m m₀ frame.l frame.l₀
    hm frame.left_limit hreal hnz
  obtain ⟨K₀,_,hK⟩ := frame.inverse_limit hm
  have hr : Tendsto (fun x i => (frame.r x i:ℂ)) L (𝓝 (fun i => (frame.r₀ i:ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp frame.right_limit) i)
  have hq : Tendsto (fun x i => (p i:ℂ)*(frame.r x i:ℂ)^2) L
      (𝓝 (fun i => (p i:ℂ)*(frame.r₀ i:ℂ)^2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_const_nhds.mul (((tendsto_pi_nhds.mp hr) i).pow 2)
  have hKr := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hK.prodMk_nhds hq)
  have hl := functional_continuous.continuousAt.tendsto.comp frame.left_limit
  have hplr : Tendsto (fun x i => p i*frame.l x i*frame.r x i) L
      (𝓝 (fun i => p i*frame.l₀ i*frame.r₀ i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (tendsto_const_nhds.mul ((tendsto_pi_nhds.mp frame.left_limit) i)).mul
      ((tendsto_pi_nhds.mp frame.right_limit) i)
  have hphi := functional_continuous.continuousAt.tendsto.comp hplr
  have hphiK := (continuous_fst.clm_comp continuous_snd).continuousAt.tendsto.comp (hphi.prodMk_nhds hK)
  have hscalar : Tendsto (fun x => 2*Complex.I*(delta x:ℂ)) L (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hd).const_mul (2*Complex.I)
  let R : X → Vec (Fin n) := fun x => (fun i => (frame.r x i:ℂ))+
    (2*Complex.I*(delta x:ℂ)) • frame.K x (fun i => (p i:ℂ)*(frame.r x i:ℂ)^2)
  let V : X → Dual (Fin n) := fun x => complexFunctional (frame.l x)+
    (2*Complex.I*(delta x:ℂ)) • (complexFunctional (fun i => p i*frame.l x i*frame.r x i)).comp (frame.K x)
  have hR : Tendsto R L (𝓝 (fun i => (frame.r₀ i:ℂ))) := by simpa [R] using hr.add (hscalar.smul hKr)
  have hV : Tendsto V L (𝓝 (complexFunctional frame.l₀)) := by
    have ht := hl.add (hscalar.smul hphiK)
    have hz : complexFunctional frame.l₀+(0:ℂ) • (complexFunctional (fun i => p i*frame.l₀ i*frame.r₀ i)).comp K₀=complexFunctional frame.l₀ := by
      ext y
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,zero_mul,add_zero]
    rw [hz] at ht
    exact ht
  have herr : Tendsto (fun x => C*(delta x^2+eta x)) L (𝓝 0) := by simpa using ((hd.pow 2).add hη).const_mul C
  have hnorm : complexFunctional frame.l₀ (fun i => (frame.r₀ i:ℂ))=1 := by
    rw [complexFunctional_apply]
    exact_mod_cast frame.center.normalized
  obtain ⟨b,B,hb,hB,ht⟩ := eventually_spectral_lengths L frame.r₀ frame.l₀
    frame.center.right_positive frame.center.left_positive hnorm R V _ hR hV herr
  refine ⟨b,B,hb,hB,?_⟩
  filter_upwards [ht] with x hx
  intro u d hest
  exact hx d.right d.left hest.2.2.2.2.2.1 hest.2.2.2.2.2.2.1

end NonSymmetricDyson.Paper.Spectral
