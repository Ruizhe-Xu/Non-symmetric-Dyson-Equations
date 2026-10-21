import Dyson.Paper.LinearEdgeActual
import Dyson.Paper.LinearEdgeScale
import Dyson.Paper.LinearEdgePoisson
import Dyson.Full.MainLinearSingular

noncomputable section
open Filter
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.LinearFrame
open Full Full.Singularities Full.SingularSpectral Full.Spectral Full.PerronContinuation
open Full.ExternalAlgebraic SingularityPoissonOrientation

/-- The support and gap Poisson scales are inserted into the actual Perron
identity (1−λ)δ=ημ. Both sides give the same square-root inverse rate. -/
theorem edge_local_from_poisson {n : ℕ} (hn : 0<n)
    (algebraic : JacobianAlgebraicity (ι := Fin n)) (puiseux : ConvergentPuiseuxTheory)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (m : ℂ → Fin n → ℂ)
    (hupper : ∀z∈upper,BasicEstimates.IsUpperSolution (m z))
    (heq : ∀z∈upper,BasicEstimates.IsDysonSolution S a z (m z))
    (τ : ℝ) (hτ : τ∉Boundary.singularUnion m)
    (frame : VaryingFrame S (Boundary.boundaryVector m) (𝓝[closedUpper] (τ:ℂ))
      (Boundary.boundaryVector m (τ:ℂ)))
    (hnz : ∀j,Boundary.boundaryVector m (τ:ℂ) j≠0)
    (ci Ci : ℝ) (hci : 0<ci) (hCi : 0<Ci)
    (hinv : ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      ci/((1-frame.lam z)+perronDensity (frame.l z) (m z))≤
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        Ci/((1-frame.lam z)+perronDensity (frame.l z) (m z)))
    (left : Bool) (c C : ℝ) (hc : 0<c) (hC : 0<C)
    (hprofile : ∀ᶠ z in 𝓝[upper] (τ:ℂ),
      if 0≤direction left*(z.re-τ) then
        c*Real.sqrt (|z.re-τ|+z.im)≤∑j,(m z j).im ∧
          (∑j,(m z j).im)≤C*Real.sqrt (|z.re-τ|+z.im)
      else
        c*z.im≤(∑j,(m z j).im)*Real.sqrt (|z.re-τ|+z.im) ∧
          (∑j,(m z j).im)*Real.sqrt (|z.re-τ|+z.im)≤C*z.im) :
    ∃ lo hi : ℝ,0<lo ∧ 0<hi ∧ ∀ᶠ z in 𝓝[upper] (τ:ℂ),∀hz : 0<z.im,
      lo/Real.sqrt (|z.re-τ|+z.im)≤
        ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖ ∧
      ‖EuclideanInverse.stabilityInverse S a z (m z) hS hz (hupper z hz) (heq z hz)‖≤
        hi/Real.sqrt (|z.re-τ|+z.im) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hfilter : 𝓝[upper] (τ:ℂ)≤𝓝[closedUpper] (τ:ℂ) :=
    nhdsWithin_mono _ (fun z hz => show 0≤z.im from le_of_lt hz)
  have hm := regular_closed_upper_limit algebraic puiseux S a hS m hupper heq τ hτ
  obtain ⟨d,D,hd,hD,hcompare⟩ := frame.density_comparison hm hnz
  let μ₀ := ∑j,frame.l₀ j*‖Boundary.boundaryVector m (τ:ℂ) j‖
  have hμ₀ : 0<μ₀ := Finset.sum_pos (fun j _ =>
    mul_pos (frame.center.left_positive j) (norm_pos_iff.mpr (hnz j))) Finset.univ_nonempty
  have hμlim := mass_tendsto (𝓝[closedUpper] (τ:ℂ)) frame.l frame.l₀
    (Boundary.boundaryVector m) _ frame.left_limit hm
  have hμlo := hμlim.eventually_const_le (show μ₀/2<μ₀ by linarith)
  have hμhi := hμlim.eventually_le_const (show μ₀<μ₀+1 by linarith)
  let b := min (d*c) ((μ₀/2)/(D*C))
  let B := (μ₀+1)/(d*c)+D*C
  have hb : 0<b := by dsimp [b]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨ci/B,Ci/b,by positivity,by positivity,?_⟩
  filter_upwards [hinv,hprofile,hcompare.filter_mono hfilter,frame.nearby.filter_mono hfilter,
    hμlo.filter_mono hfilter,hμhi.filter_mono hfilter,self_mem_nhdsWithin]
      with z hinvz hp hcpr hf hμlo hμhi hz
  intro hz'
  have hext := Boundary.family_extension_agrees S a hS m hupper heq z hz
  have hf' : PerronData (saturatedMatrix S (m z)) (frame.lam z) (frame.r z) (frame.l z) := by
    simpa only [hext] using hf
  have hcp := hcpr (fun j => by rw [hext]; exact (hupper z hz j).le)
  rw [hext] at hcp hμlo hμhi
  obtain ⟨hδ,hlam⟩ := perron_eigenvalue_identity S a z (m z) (hupper z hz) (heq z hz)
    (frame.l z) (frame.lam z) hf'.left_positive hf'.left_eigen
  have ha : 0≤1-frame.lam z := by
    have hh := perron_eigenvalue_lt_one S a z (m z) hz (hupper z hz) (heq z hz)
      (frame.l z) (frame.lam z) hf'.left_positive hf'.left_eigen
    linarith
  change 0<perronDensity (frame.l z) (m z) at hδ
  change frame.lam z=1-z.im*(∑j,frame.l z j*‖m z j‖)/perronDensity (frame.l z) (m z) at hlam
  have hid : (1-frame.lam z)*perronDensity (frame.l z) (m z)=
      (∑j,frame.l z j*‖m z j‖)*z.im := by
    rw [hlam]
    field_simp [hδ.ne']
    <;> ring
  let t := Real.sqrt (|z.re-τ|+z.im)
  have ht : 0<t := Real.sqrt_pos.mpr (by positivity)
  have hηt : z.im≤t^2 := by dsimp [t]; rw [Real.sq_sqrt (by positivity)]; linarith [abs_nonneg (z.re-τ)]
  have hscale : b*t≤(1-frame.lam z)+perronDensity (frame.l z) (m z) ∧
      (1-frame.lam z)+perronDensity (frame.l z) (m z)≤B*t := by
    by_cases hs : 0≤direction left*(z.re-τ)
    · rw [if_pos hs] at hp
      have hlo : (d*c)*t≤perronDensity (frame.l z) (m z) := by
        calc
          (d*c)*t≤d*(∑j,(m z j).im) := by simpa [t,mul_assoc] using mul_le_mul_of_nonneg_left hp.1 hd.le
          _ ≤ _ := hcp.1
      have hhi : perronDensity (frame.l z) (m z)≤(D*C)*t :=
        hcp.2.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hp.2 hD.le)
      have hbnd := LinearEdgeScale.support_scale ha ht (mul_pos hd hc) hz.le hηt hμhi
        (by positivity : 0≤μ₀+1) hid hlo hhi
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le).trans hbnd.1,hbnd.2⟩
    · rw [if_neg hs] at hp
      have hlo : (d*c)*z.im≤perronDensity (frame.l z) (m z)*t := by
        calc
          (d*c)*z.im≤d*((∑j,(m z j).im)*t) := by nlinarith [mul_le_mul_of_nonneg_left hp.1 hd.le]
          _ ≤ perronDensity (frame.l z) (m z)*t := by nlinarith [mul_le_mul_of_nonneg_right hcp.1 ht.le]
      have hhi : perronDensity (frame.l z) (m z)*t≤(D*C)*z.im := by
        calc
          _ ≤ D*((∑j,(m z j).im)*t) := by nlinarith [mul_le_mul_of_nonneg_right hcp.2 ht.le]
          _ ≤ (D*C)*z.im := by nlinarith [mul_le_mul_of_nonneg_left hp.2 hD.le]
      have hbnd := LinearEdgeScale.gap_scale ha ht (mul_pos hd hc) (mul_pos hD hC)
        (half_pos hμ₀) hz hηt hμlo hμhi hid hlo hhi
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le).trans hbnd.1,hbnd.2⟩
  exact LinearEdgeScale.inverse_scale ht hb hB hci.le hCi.le hscale (hinvz hz')

/-- Euclidean and horizontal-plus-height distances have the same square-root
rate, with an explicit factor two sufficient for the two-sided comparison. -/
theorem sqrt_local_to_distance {τ lo hi : ℝ} {z : ℂ} {N : ℝ}
    (hz : 0<z.im) (hlo : 0≤lo) (hhi : 0≤hi)
    (h : lo/Real.sqrt (|z.re-τ|+z.im)≤N ∧ N≤hi/Real.sqrt (|z.re-τ|+z.im)) :
    (lo/2)/‖z-(τ:ℂ)‖^((1:ℝ)/2)≤N ∧ N≤hi/‖z-(τ:ℂ)‖^((1:ℝ)/2) := by
  have hn : 0<‖z-(τ:ℂ)‖ := hz.trans_le (by simpa using Complex.im_le_norm (z-(τ:ℂ)))
  have hq : 0 < |z.re-τ|+z.im := by positivity
  have hl : ‖z-(τ:ℂ)‖≤|z.re-τ|+z.im := by
    simpa [abs_of_pos hz] using Complex.norm_le_abs_re_add_abs_im (z-(τ:ℂ))
  have hu : |z.re-τ|+z.im≤2*‖z-(τ:ℂ)‖ := by
    have hr := Complex.abs_re_le_norm (z-(τ:ℂ))
    have hi := Complex.im_le_norm (z-(τ:ℂ))
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero] at hr hi
    linarith
  have hnroot := Real.sqrt_pos.mpr hn
  have hqroot := Real.sqrt_pos.mpr hq
  have hrootlo := Real.sqrt_le_sqrt hl
  have hroothi : Real.sqrt (|z.re-τ|+z.im)≤2*Real.sqrt ‖z-(τ:ℂ)‖ := by
    nlinarith [Real.sq_sqrt hq.le,Real.sq_sqrt hn.le,Real.sqrt_nonneg (|z.re-τ|+z.im)]
  rw [←Real.sqrt_eq_rpow]
  constructor
  · have hh : lo/(2*Real.sqrt ‖z-(τ:ℂ)‖)≤lo/Real.sqrt (|z.re-τ|+z.im) :=
      div_le_div_of_nonneg_left hlo hqroot hroothi
    calc
      (lo/2)/Real.sqrt ‖z-(τ:ℂ)‖≤lo/Real.sqrt (|z.re-τ|+z.im) := by simpa [div_div] using hh
      _ ≤ N := h.1
  · exact h.2.trans (div_le_div_of_nonneg_left hhi hnroot hrootlo)

end NonSymmetricDyson.Paper.LinearFrame
