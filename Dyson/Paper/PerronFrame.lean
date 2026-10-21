import Dyson.Paper.SingularitiesNormalization
import Dyson.Paper.RegularityBounds
import Dyson.Paper.Foundations
import Dyson.Full.PerronSpectrum

/-! The complete F-PF lemma on an arbitrary bounded-solution strip.
The same uniquely normalized actual pair supplies the spectral radius,
imaginary-part identity, and uniform component bounds. -/
noncomputable section
open scoped BigOperators Topology
open Set
namespace NonSymmetricDyson.Paper.PerronFrame
open Full Full.Singularities Full.PerronContinuation

private theorem real_eigenvector_multiple {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) (r l R : Fin n → ℝ)
    (hd : PerronData A lam r l)
    (hR : ∀ i,∑ j,A i j*R j=lam*R i) :
    ∀ i,R i=(∑ j,l j*R j)*r i := by
  have he : complexMatrixOperator A (fun i => (R i:ℂ))=
      (lam:ℂ) • (fun i => (R i:ℂ)) := by
    ext i
    change (∑ j,(A i j:ℂ)*(R j:ℂ))=(lam:ℂ)*(R i:ℂ)
    exact_mod_cast hR i
  have hs := hd.simple _ he
  have hf : complexFunctional l (fun j => (R j:ℂ))=((∑ j,l j*R j:ℝ):ℂ) := by
    simp [complexFunctional,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [hf] at hs
  intro i
  have hh := congrArg Complex.re (congrFun hs i)
  simpa [complexFunctional_apply] using hh

/-- The simultaneous normalizations really determine both positive vectors
and the eigenvalue. The auxiliary transpose PF theorem is ordinary matrix
theory, not a Dyson-specific uniqueness premise. -/
theorem normalized_pair_unique
    (perron : ExternalPerronExistence) {n : ℕ} (hn : 0<n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Manuscript.PositivityCorrection.Nonnegative A)
    (hirr : Manuscript.PositivityCorrection.Irreducible A)
    (lam rho : ℝ) (r l R L : Fin n → ℝ)
    (hd : PerronData A lam r l) (hRp : ∀ i,0<R i)
    (hpair : ∑ i,L i*R i=1)
    (hAR : ∀ i,∑ j,A i j*R j=rho*R i)
    (hLA : ∀ j,∑ i,L i*A i j=rho*L j)
    (hrnorm : ∑ i,r i^2=1) (hRnorm : ∑ i,R i^2=1) :
    rho=lam ∧ R=r ∧ L=l := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have heq := positive_perron_value_unique A l R lam rho hd.left_positive
    hRp hd.left_eigen hAR
  subst rho
  have hR := real_eigenvector_multiple A lam r l R hd hAR
  let t : ℝ := ∑ j,l j*R j
  have ht : 0<t := Finset.sum_pos (fun j _ => mul_pos (hd.left_positive j)
    (hRp j)) Finset.univ_nonempty
  have hs : t^2=1 := by
    calc
      t^2 = t^2*(∑ i,r i^2) := by rw [hrnorm,mul_one]
      _ = ∑ i,(t*r i)^2 := by simp [mul_pow,Finset.mul_sum]
      _ = ∑ i,R i^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun x : ℝ => x^2) (hR i).symm
      _ = 1 := hRnorm
  have ht1 : t=1 := by nlinarith
  have hReq : R=r := by
    funext i
    simpa only [show (∑ j,l j*R j)=1 from ht1,one_mul] using hR i
  subst R
  obtain ⟨g,u,v,hg,hu,hv,hvu,hAu,hvA,hsm⟩ := perron n hn A.transpose
    (fun i j => hA j i) (irreducible_transpose A hirr)
  have hlg : lam=g := positive_perron_value_unique A.transpose r u lam g
    hd.right_positive hu (fun j => by simpa [mul_comm] using hd.right_eigen j) hAu
  subst g
  have hT : PerronData A.transpose lam u v :=
    ⟨hd.eigenvalue_positive,hu,hv,hvu,hAu,hvA,by
      intro x hx
      simpa [complexFunctional] using hsm x hx⟩
  have hL := real_eigenvector_multiple A.transpose lam u v L hT
    (fun i => by simpa [mul_comm] using hLA i)
  have hl := real_eigenvector_multiple A.transpose lam u v l hT
    (fun i => by simpa [mul_comm] using hd.left_eigen i)
  have hpos : 0<∑ i,u i*r i := Finset.sum_pos
    (fun i _ => mul_pos (hu i) (hd.right_positive i)) Finset.univ_nonempty
  have hp : (∑ j,v j*L j)*(∑ i,u i*r i)=(∑ j,v j*l j)*(∑ i,u i*r i) := by
    calc
      _ = ∑ i,L i*r i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hL i]
        ring
      _ = 1 := hpair
      _ = ∑ i,l i*r i := hd.normalized.symm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hl i]
        ring
  have htEq := mul_right_cancel₀ hpos.ne' hp
  refine ⟨rfl,rfl,?_⟩
  funext i
  rw [hL,hl,htEq]

/-- One actual normalized Perron pair exists at every upper point. -/
theorem normalized_saturated_data
    (perron : ExternalPerronExistence)
    (frobenius : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0<n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : Fin n → ℂ) (hm : ∀ i,m i≠0) :
    ∃ lam r l,PerronData (saturatedMatrix S m) lam r l ∧
      (∑ i,r i^2=1) ∧ ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖=1 ∧
      IsGreatest {t : ℝ | ∃ z : ℂ,
        ((saturatedMatrix S m).map Complex.ofRealHom).charpoly.IsRoot z ∧ ‖z‖=t} lam := by
  obtain ⟨lam,r,l,_,hr,hl,hpair,hFr,hlF,hsimple⟩ :=
    saturatedMatrix_perron_data perron hn S hS hirr m hm
  obtain ⟨hlam,hspec,_⟩ := saturated_perron_spectrum frobenius hn S hS hirr m hm l lam hl hlF
  have hd : PerronData (saturatedMatrix S m) lam r l :=
    ⟨hlam,hr,hl,hpair,hFr,hlF,hsimple⟩
  obtain ⟨R,L,hD,hunit,hnorm⟩ := SingularitiesNormalization.normalize_perron_data hn _ lam r l hd
  exact ⟨lam,R,L,hD,hunit,hnorm,hspec⟩

/-- `lem:F-PF`: uniform constants precede z, and the same pair has all the
source's normalizations, exact eigenvalue formula and actual spectral radius.
No compactness or upper bound on the real interval is imposed. -/
theorem saturated_strip_frame
    (perron : ExternalPerronExistence)
    (frobenius : ClassicalFrobenius.ExternalCitedFrobeniusTheory)
    {n : ℕ} (hn : 0<n)
    (external : Full.Foundations.ExternalStieltjesTheory (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (I : Set ℝ) (Φ : ℝ)
    (hbound : ∀ z : ℂ,z.re∈I → 0<z.im →
      ‖(WithLp.toLp 2 (Foundations.solution S a hS z) : EuclideanSpace ℂ (Fin n))‖≤Φ) :
    let m := Foundations.solution S a hS
    ∃ b B : ℝ,0<b ∧ 0<B ∧ ∀ z : ℂ,z.re∈I → 0<z.im →
      ∃ lam r l,PerronData (saturatedMatrix S (m z)) lam r l ∧
        (∑ i,r i^2=1) ∧ ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖=1 ∧
        IsGreatest {t : ℝ | ∃ w : ℂ,
          ((saturatedMatrix S (m z)).map Complex.ofRealHom).charpoly.IsRoot w ∧ ‖w‖=t} lam ∧
        lam=1-z.im*(∑ i,l i*‖m z i‖)/(∑ i,l i*((m z i).im/‖m z i‖)) ∧
        lam<1 ∧ (∀ i,b≤r i ∧ r i≤B ∧ b≤l i ∧ l i≤B) ∧
        ∀ rho R L,(∀ i,0<R i) → (∑ i,L i*R i=1) →
          (∀ i,∑ j,saturatedMatrix S (m z) i j*R j=rho*R i) →
          (∀ j,∑ i,L i*saturatedMatrix S (m z) i j=rho*L j) →
          (∑ i,R i^2=1) → rho=lam ∧ R=r ∧ L=l := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let m := Foundations.solution S a hS
  let μ := Foundations.measure S a hn external hS
  have hu : ∀ z : ℂ,0<z.im → BasicEstimates.IsUpperSolution (m z) :=
    fun z hz => Foundations.solution_upper S a hS hz
  have he : ∀ z : ℂ,0<z.im → BasicEstimates.IsDysonSolution S a z (m z) :=
    fun z hz => Foundations.solution_equation S a hS hz
  obtain ⟨c,C,β,hc,hC,hβ,hbounds⟩ := RegularityBounds.family_interior_global_bounds hn S a hS hirr
    m hu he μ (fun i => (Foundations.measure_spec S a hn external hS i).1)
    (fun i => (Foundations.measure_spec S a hn external hS i).2.1)
    (Foundations.sigma S a) (Foundations.sigma_nonnegative S a)
    (fun i => (Foundations.measure_spec S a hn external hS i).2.2.1)
    I (max 0 Φ) (le_max_left _ _) (fun z hzI hz i =>
      ((PiLp.norm_apply_le (WithLp.toLp 2 (m z)) i).trans (hbound z hzI hz)).trans (le_max_right _ _))
  obtain ⟨cr,hcr,cl,hcl,lo,hlo,hi,hhi,hpf⟩ :=
    uniform_saturated_perron_bounds hn S hS hirr c C hc hC
  refine ⟨min cr cl,max 1 (1/cr),lt_min hcr hcl,
    lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _),?_⟩
  intro z hzI hz
  have hm : ∀ i,m z i≠0 := BasicEstimates.component_ne_zero (hu z hz)
  obtain ⟨lam,r,l,hd,hnorm,heucl,hspec⟩ := normalized_saturated_data perron frobenius hn S hS hirr (m z) hm
  have hs : 0<1+‖z‖ := by positivity
  have hp := hpf (1+‖z‖) (m z) r l lam hs
    (fun i => by simpa [mul_comm] using (div_le_iff₀ hs).mp ((hbounds z hzI hz).1 i).1)
    (fun i => by simpa [mul_comm] using (le_div_iff₀ hs).mp ((hbounds z hzI hz).1 i).2)
    hd.right_positive hd.left_positive hd.right_eigen hd.left_eigen hnorm hd.normalized
  refine ⟨lam,r,l,hd,hnorm,heucl,hspec,
    (perron_eigenvalue_identity S a z (m z) (hu z hz) (he z hz) l lam hd.left_positive hd.left_eigen).2,
    perron_eigenvalue_lt_one S a z (m z) hz (hu z hz) (he z hz) l lam hd.left_positive hd.left_eigen,
    ?_,?_⟩
  · intro i
    exact ⟨(min_le_left _ _).trans (hp.1 i).1,
      (hp.1 i).2.trans (le_max_left _ _),(min_le_right _ _).trans (hp.2.1 i).1,
      (hp.2.1 i).2.trans (le_max_right _ _)⟩
  · intro rho R L hRp hpair hAR hLA hR
    exact normalized_pair_unique perron hn _ (saturatedMatrix_nonnegative S hS _)
      (saturatedMatrix_irreducible S hS hirr _ hm) lam rho r l R L hd hRp hpair hAR hLA hnorm hR

end NonSymmetricDyson.Paper.PerronFrame
