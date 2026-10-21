import Dyson.Full.SpectralExpansion

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Full.SingularSpectral
open Singularities Spectral
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem functional_left_eigen_general (F : Matrix ι ι ℝ) (l : ι → ℝ)
    (lam : ℝ) (hl : ∀ j, ∑ i, l i*F i j=lam*l j) (x : ι → ℂ) :
    complexFunctional l (complexMatrixOperator F x)=(lam:ℂ)*complexFunctional l x := by
  simp only [complexFunctional_apply,complexMatrixOperator_apply]
  calc
    (∑ i, (l i:ℂ)*∑ j,(F i j:ℂ)*x j) =
        ∑ i, ∑ j, ((l i:ℂ)*(F i j:ℂ))*x j := by simp [Finset.mul_sum,mul_assoc]
    _ = ∑ j, (∑ i,(l i:ℂ)*(F i j:ℂ))*x j := by
      rw [Finset.sum_comm]
      simp [Finset.sum_mul]
    _ = ∑ j, ((lam:ℂ)*(l j:ℂ))*x j := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact_mod_cast hl j
    _ = _ := by simp [Finset.mul_sum,mul_assoc]

/-- All model-specific hypotheses of the general spectral Taylor input are
verified uniformly from actual Perron data and the actual Dyson equation.
Only bounded frame data and small δ,η,1−λ remain to be supplied by continuity. -/
theorem dyson_spectral_expansion_uniform
    (external : QuadraticSimpleSpectralPerturbationTheory (ι := ι))
    (B b : ℝ) (hB : 0 < B) (hb : 0 < b) :
    ∃ ε ρ C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < ρ ∧ 0 < C ∧
    ∀ (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m : ι → ℂ)
      (p r l : ι → ℝ) (K : End ι) (lam : ℝ),
      (∀ i, m i≠0) → BasicEstimates.IsDysonSolution S a z m →
      (∀ i, 0 ≤ normalizedImag m i) → (∀ i, p i^2=1) → (∀ i, 0 ≤ p i*(m i).re) →
      ‖(fun i => (r i:ℂ))‖ ≤ B → ‖complexFunctional l‖ ≤ B → ‖K‖ ≤ B →
      ‖(fun i => (‖m i‖:ℂ))‖ ≤ B → (∀ i, b ≤ l i) →
      (∑ i, l i*r i=1) →
      (∀ i, ∑ j, (‖m i‖*S i j*‖m j‖)*r j=lam*r i) →
      (∀ j, ∑ i, l i*(‖m i‖*S i j*‖m j‖)=lam*l j) →
      IsRestrictedInverse (saturatedOperator S m).toLinearMap K.toLinearMap
        (complexFunctional l).toLinearMap (fun i => (r i:ℂ)) →
      (∀ x : ι → ℝ, ∃ y : ι → ℝ, K (fun i => (x i:ℂ))=fun i => (y i:ℂ)) →
      perronDensity l m ≤ ε → 0 ≤ z.im → z.im ≤ ε → |1-lam| ≤ ε →
      ∃ (u : ι → ℝ) (d : SimpleSpectralSplit (reducedOperator S m)),
        K (fun i => (p i:ℂ)*(r i:ℂ)^2)=(fun i => (u i:ℂ)) ∧
        HasDysonSpectralEstimates S m p r l u K lam (perronDensity l m) z.im ρ C d := by
  let P : ℝ := 1+8*(B^3+(B^2)^3)+2*(B^2)*(2+B)
  let G : ℝ := 1+B+2*B+2*B^2+2*b⁻¹+P+B^2
  have hP : 0 < P := by dsimp [P]; positivity
  have hG : 0 < G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have hBG : B ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have h2BG : 2*B ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have h2B2G : 2*B^2 ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have hbG : 2*b⁻¹ ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have hPG : P ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  have hB2G : B^2 ≤ G := by dsimp [G]; nlinarith [inv_nonneg.mpr hb.le, sq_nonneg B]
  obtain ⟨ε,ρ,C,hε,hε1,hρ,hC,ht⟩ := dyson_spectral_expansion external G hG
  refine ⟨ε,ρ,C,hε,hε1,hρ,hC,?_⟩
  intro S a z m p r l K lam hm hsol hv hp hsign hr hl hKb hq hlow hnorm
    hright hleft hK hreal hδε hη hηε hlam
  let δ : ℝ := perronDensity l m
  have hlpos : ∀ i, 0 ≤ l i := fun i => hb.le.trans (hlow i)
  have hδ : 0 ≤ δ := perron_density_nonneg l m hlpos hv
  have hδ1 : δ ≤ 1 := hδε.trans hε1
  have hη1 : z.im ≤ 1 := hηε.trans hε1
  obtain ⟨u,hu⟩ := hreal (fun i => p i*r i^2)
  have hKu : K (fun i => (p i:ℂ)*(r i:ℂ)^2)=fun i => (u i:ℂ) := by simpa using hu
  obtain ⟨t,htq⟩ := hreal (fun i => ‖m i‖)
  have hri : ∀ i, |r i| ≤ B := fun i => by
    simpa using (norm_le_pi_norm (fun j => (r j:ℂ)) i).trans hr
  have hti : ∀ i, |t i| ≤ B^2 := by
    intro i
    have hh := (norm_le_pi_norm (K (fun j => (‖m j‖:ℂ))) i).trans
      ((K.le_opNorm _).trans (mul_le_mul hKb hq (norm_nonneg _) hB.le))
    simpa [htq,pow_two] using hh
  have hnormC : complexFunctional l (fun i => (r i:ℂ))=1 := by
    simpa [complexFunctional_apply,← Complex.ofReal_mul,← Complex.ofReal_sum] using
      congrArg Complex.ofReal hnorm
  have hrightC : saturatedOperator S m (fun i => (r i:ℂ))=
      (lam:ℂ) • (fun i => (r i:ℂ)) := by
    ext i
    change (∑ j, ((‖m i‖*S i j*‖m j‖:ℝ):ℂ)*(r j:ℂ))=(lam:ℂ)*(r i:ℂ)
    exact_mod_cast hright i
  have hleftC : ∀ x, complexFunctional l (saturatedOperator S m x)=
      (lam:ℂ)*complexFunctional l x := functional_left_eigen_general _ l lam hleft
  have hμ : ∑ i, l i*‖m i‖ ≤ B^2 := by
    have he : complexFunctional l (fun i => (‖m i‖:ℂ))=((∑ i, l i*‖m i‖:ℝ):ℂ) := by
      simp [complexFunctional_apply]
    have hh := (complexFunctional l).le_opNorm (fun i => (‖m i‖:ℂ))
    rw [he] at hh
    have hn : 0 ≤ ∑ i, l i*‖m i‖ := Finset.sum_nonneg (fun i _ => mul_nonneg (hlpos i) (norm_nonneg _))
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn] at hh
    simpa only [pow_two] using hh.trans (mul_le_mul hl hq (norm_nonneg _) hB.le)
  have hprod : |1-lam| * δ ≤ G*z.im := by
    rw [show δ=perronDensity l m from rfl,
      perron_scaled_height S a z m hm hsol l lam hη hlpos hv hleft]
    nlinarith [mul_le_mul_of_nonneg_left (hμ.trans hB2G) hη]
  have hphase : ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι)‖ ≤ G*δ :=
    (phase_operator_bound m hm δ b⁻¹ hδ (inv_nonneg.mpr hb.le)
      (normalizedImag_le_density l m b hb hlow hv)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hbG hδ])
  have htaylor : ‖phaseOperator m-ContinuousLinearMap.id ℂ (Vec ι)-
      (δ:ℂ) • firstPhase p r-((δ:ℂ)^2) • secondPhase r‖ ≤ G*(δ^3+z.im) :=
    (phase_operator_taylor m hm p r t δ z.im B (B^2) hp hsign hδ hδ1 hη hη1
      hB.le (sq_nonneg _) hri hti (imaginary_direction_real S a z m hm hsol r l t K hK htq)).trans
        (mul_le_mul_of_nonneg_right hPG (by positivity))
  obtain ⟨d,hd⟩ := ht S m p r l u K lam δ z.im
    (hr.trans hBG) (hl.trans hBG) (hKb.trans hBG)
    ((firstPhase_norm_le p r B hB.le hp hri).trans h2BG)
    ((secondPhase_norm_le r B hB.le hri).trans h2B2G)
    hnormC hrightC hleftC hK hp hKu hδ hδε hη hηε hlam hprod hphase htaylor
  exact ⟨u,d,hKu,hd⟩

end NonSymmetricDyson.Full.SingularSpectral
