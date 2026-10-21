import Dyson.Full.PerronExistence
import Dyson.Full.RestrictedInverseExistence

/-! Continuous Perron frames for the actual saturated Dyson matrices.
The external statement is solely the ordinary local continuous
Perron--Frobenius theorem on finite real matrix space. The actual family,
frontier eigenvalue, complementary invertibility and inverse bounds are
constructed internally. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Full.PerronContinuation
open Singularities

structure PerronData {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (r l : Fin n → ℝ) : Prop where
  eigenvalue_positive : 0 < lam
  right_positive : ∀ i, 0 < r i
  left_positive : ∀ i, 0 < l i
  normalized : ∑ i, l i*r i=1
  right_eigen : ∀ i, ∑ j, A i j*r j=lam*r i
  left_eigen : ∀ j, ∑ i, l i*A i j=lam*l j
  simple : ∀ x : Fin n → ℂ, complexMatrixOperator A x=(lam:ℂ) • x →
    x=complexFunctional l x • (fun i => (r i:ℂ))

/-- Local continuous positive normalized eigenvectors and their simple
eigenspace, for arbitrary finite real matrices near an irreducible
nonnegative matrix. This contains no Dyson solution or stability conclusion. -/
def ExternalContinuousPerron : Prop :=
  ∀ (n : ℕ) (_hn : 0<n) (A : Matrix (Fin n) (Fin n) ℝ),
    Manuscript.PositivityCorrection.Nonnegative A →
    Manuscript.PositivityCorrection.Irreducible A →
    ∃ (U : Set (Matrix (Fin n) (Fin n) ℝ)), IsOpen U ∧ A∈U ∧
      ∃ (lam : Matrix (Fin n) (Fin n) ℝ → ℝ)
        (r l : Matrix (Fin n) (Fin n) ℝ → Fin n → ℝ),
        ContinuousOn lam U ∧ ContinuousOn r U ∧ ContinuousOn l U ∧
        ∀ B∈U, PerronData B (lam B) (r B) (l B)

structure ContinuousFrame {X : Type*} [TopologicalSpace X] {n : ℕ}
    (F : X → Matrix (Fin n) (Fin n) ℝ) (x₀ : X) where
  lam : X → ℝ
  r : X → Fin n → ℝ
  l : X → Fin n → ℝ
  lam_continuous : ContinuousAt lam x₀
  right_continuous : ContinuousAt r x₀
  left_continuous : ContinuousAt l x₀
  center : PerronData (F x₀) (lam x₀) (r x₀) (l x₀)
  nearby : ∀ᶠ x in 𝓝 x₀, PerronData (F x) (lam x) (r x) (l x)

theorem continuous_frame_exists (external : ExternalContinuousPerron)
    {X : Type*} [TopologicalSpace X] {n : ℕ} (hn : 0<n)
    (F : X → Matrix (Fin n) (Fin n) ℝ) (x₀ : X) (hF : ContinuousAt F x₀)
    (hpos : Manuscript.PositivityCorrection.Nonnegative (F x₀))
    (hirr : Manuscript.PositivityCorrection.Irreducible (F x₀)) :
    Nonempty (ContinuousFrame F x₀) := by
  obtain ⟨U,hU,hmem,lam,r,l,hlam,hr,hl,hdata⟩ := external n hn (F x₀) hpos hirr
  have hnear : ∀ᶠ x in 𝓝 x₀, F x∈U := hF.tendsto.eventually (hU.mem_nhds hmem)
  refine ⟨⟨fun x => lam (F x),fun x => r (F x),fun x => l (F x),
    (hlam.continuousAt (hU.mem_nhds hmem)).comp hF,
    (hr.continuousAt (hU.mem_nhds hmem)).comp hF,
    (hl.continuousAt (hU.mem_nhds hmem)).comp hF,hdata _ hmem,?_⟩⟩
  filter_upwards [hnear] with x hx
  exact hdata _ hx

theorem saturatedMatrix_continuousAt {X : Type*} [TopologicalSpace X] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (m : X → Fin n → ℂ) (x₀ : X)
    (hm : ContinuousAt m x₀) : ContinuousAt (fun x => saturatedMatrix S (m x)) x₀ := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (((continuous_apply i).continuousAt.comp hm).norm.mul continuousAt_const).mul
    (((continuous_apply j).continuousAt.comp hm).norm)

theorem saturated_frame_exists (external : ExternalContinuousPerron)
    {X : Type*} [TopologicalSpace X] {n : ℕ} (hn : 0<n)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : Manuscript.PositivityCorrection.Nonnegative S)
    (hirr : Manuscript.PositivityCorrection.Irreducible S)
    (m : X → Fin n → ℂ) (x₀ : X) (hm : ContinuousAt m x₀)
    (hnz : ∀ i, m x₀ i≠0) :
    Nonempty (ContinuousFrame (fun x => saturatedMatrix S (m x)) x₀) :=
  continuous_frame_exists external hn _ x₀ (saturatedMatrix_continuousAt S m x₀ hm)
    (saturatedMatrix_nonnegative S hS _) (saturatedMatrix_irreducible S hS hirr _ hnz)

variable {X : Type*} [TopologicalSpace X] {n : ℕ} [Nonempty (Fin n)]

theorem matrixOperator_continuous :
    Continuous (complexMatrixOperator (ι := Fin n)) := by
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_pi
  intro i
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => ∑ j, (A i j:ℂ)*v j)
  apply continuous_finset_sum
  intro j hj
  exact (Complex.continuous_ofReal.comp ((continuous_apply j).comp
    (continuous_apply i))).mul continuous_const

theorem matrixOperator_continuousAt (F : X → Matrix (Fin n) (Fin n) ℝ)
    (x₀ : X) (hF : ContinuousAt F x₀) :
    ContinuousAt (fun x => complexMatrixOperator (F x)) x₀ :=
  matrixOperator_continuous.continuousAt.comp hF

theorem functional_continuous :
    Continuous (complexFunctional (ι := Fin n)) := by
  apply continuous_clm_apply.mpr
  intro v
  simp only [complexFunctional_apply]
  apply continuous_finset_sum
  intro i hi
  exact (Complex.continuous_ofReal.comp (continuous_apply i)).mul continuous_const

theorem functional_continuousAt (l : X → Fin n → ℝ) (x₀ : X)
    (hl : ContinuousAt l x₀) : ContinuousAt (fun x => complexFunctional (l x)) x₀ :=
  functional_continuous.continuousAt.comp hl

theorem functional_left_eigen (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (lam : ℝ) (hl : ∀ j, ∑ i, l i*A i j=lam*l j) (x : Fin n → ℂ) :
    complexFunctional l (complexMatrixOperator A x)=(lam:ℂ)*complexFunctional l x := by
  simp only [complexFunctional_apply,complexMatrixOperator_apply]
  calc
    (∑ i, (l i:ℂ)*∑ j,(A i j:ℂ)*x j) =
        ∑ i, ∑ j, ((l i:ℂ)*(A i j:ℂ))*x j := by simp [Finset.mul_sum,mul_assoc]
    _ = ∑ j, (∑ i,(l i:ℂ)*(A i j:ℂ))*x j := by
      rw [Finset.sum_comm]
      simp [Finset.sum_mul]
    _ = ∑ j, ((lam:ℂ)*(l j:ℂ))*x j := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      exact_mod_cast hl j
    _ = _ := by simp [Finset.mul_sum,mul_assoc]

end NonSymmetricDyson.Full.PerronContinuation
