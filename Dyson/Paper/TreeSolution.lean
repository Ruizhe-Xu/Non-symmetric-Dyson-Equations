import Dyson.Paper.TreeModel
import Dyson.Paper.TreeSpectral
import Dyson.Paper.Foundations

/-! Root Green functions of the actual type-word operators satisfy the
Dyson equation. The only external input is the general bounded self-adjoint
spectral principle; the tree, operators and Schur recurrence are proved. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory
namespace NonSymmetricDyson.Paper.TreeSolution
universe u
variable {ι : Type u} [Fintype ι]
variable (S : ι → ι → ℝ) (a : ι → ℝ)
variable (hS : ∀ i j, 0 ≤ S i j) (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
variable (ha : ∀ i, |a i| ≤ A) (hr : ∀ i, (∑ j, S i j) ≤ R)
variable (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{u})

def data (i : ι) : TreeSpectral.ResolventMeasureData
    (TreeModel.jacobi S a hS A R hA hR ha hr i) :=
  (spectral _ (TreeModel.jacobi_selfAdjoint S a hS A R hA hR ha hr i)).some

def transform (z : ℂ) (i : ι) : ℂ :=
  TreeModel.root S i ((data S a hS A R hA hR ha hr spectral i).green z (TreeModel.delta S i))

include hS A R hA hR ha hr spectral

theorem transform_inner (z : ℂ) (i : ι) :
    transform S a hS A R hA hR ha hr spectral z i =
      inner ℂ (TreeModel.delta S i)
        ((data S a hS A R hA hR ha hr spectral i).green z (TreeModel.delta S i)) :=
  (TreeModel.inner_delta S i _).symm

theorem transform_upper {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsUpperSolution (transform S a hS A R hA hR ha hr spectral z) := by
  intro i
  rw [transform_inner]
  apply TreeSpectral.ResolventMeasureData.scalar_im_pos _ z hz
  intro he
  have hh := TreeModel.norm_delta S i
  rw [he,norm_zero] at hh
  exact zero_ne_one hh

/-- Root deletion for the concrete tree yields the original finite system. -/
theorem transform_equation {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsDysonSolution S a z (transform S a hS A R hA hR ha hr spectral z) := by
  intro i
  let D := data S a hS A R hA hR ha hr spectral
  have hs := TreeSchur.weighted_branch_resolvent_identity
    (TreeModel.jacobi S a hS A R hA hR ha hr i)
    (fun j : TreeWords.Word.Child (.nil i) => TreeModel.jacobi S a hS A R hA hR ha hr j.val)
    (TreeModel.root S i)
    (fun j => TreeModel.branch S j.property)
    (fun j => TreeModel.root S j.val)
    (fun j => TreeModel.delta S j.val)
    (fun j => Real.sqrt (S i j.val)) (TreeModel.delta S i) (a i : ℂ) z
    ((D i).shifted z hz) (fun j => (D j.val).shifted z hz)
    ((D i).shifted_apply z hz) (fun j => (D j.val).shifted_apply z hz)
    (TreeModel.jacobi_root S a hS A R hA hR ha hr i)
    (fun j => TreeModel.jacobi_branch S a hS A R hA hR ha hr j.property)
    (TreeModel.root_delta S i) (fun j => TreeModel.branch_delta S j.property)
  have hg (j : ι) : (D j).green z = ((D j).shifted z hz).symm.toContinuousLinearMap :=
    (D j).green_eq z hz
  have hm (j : ι) : TreeModel.root S j (((D j).shifted z hz).symm (TreeModel.delta S j)) =
      transform S a hS A R hA hR ha hr spectral z j := by
    unfold transform
    rw [show (data S a hS A R hA hR ha hr spectral j).green z =
      ((D j).shifted z hz).symm.toContinuousLinearMap from hg j]
    rfl
  rw [hm] at hs
  rw [hs.2]
  congr 1
  calc
    _ = ∑ j : {j : ι // 0 < S i j}, (S i j.val : ℂ) *
        transform S a hS A R hA hR ha hr spectral z j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.sq_sqrt (hS i j.val),hm]
    _ = _ := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 0 < S i j)
        (fun j => (S i j : ℂ) * transform S a hS A R hA hR ha hr spectral z j)]
      have he : (∑ j : {j : ι // ¬0 < S i j}, (S i j.val : ℂ) *
          transform S a hS A R hA hR ha hr spectral z j.val) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hzj : S i j.val = 0 := le_antisymm (le_of_not_gt j.property) (hS i j.val)
        simp [hzj]
      rw [he,add_zero]

/-- Existence is obtained from the tree; only the already proved finite
Dyson uniqueness theorem is used to identify any competing solution. -/
theorem wellPosedness : Model.WellPosednessTarget S a := by
  intro z hz
  refine ⟨transform S a hS A R hA hR ha hr spectral z,
    ⟨transform_upper S a hS A R hA hR ha hr spectral hz,
      transform_equation S a hS A R hA hR ha hr spectral hz⟩,?_⟩
  intro m hm
  exact Uniqueness.upper_half_plane_unique hS hz hm.1
    (transform_upper S a hS A R hA hR ha hr spectral hz) hm.2
    (transform_equation S a hS A R hA hR ha hr spectral hz)

theorem canonical_eq {z : ℂ} (hz : 0 < z.im) :
    GlobalWellPosedness.solution S a hS z = transform S a hS A R hA hR ha hr spectral z :=
  GlobalWellPosedness.solution_eq_of_upper_solution a hS hz
    (transform_upper S a hS A R hA hR ha hr spectral hz)
    (transform_equation S a hS A R hA hR ha hr spectral hz)

theorem analytic_transform :
    AnalyticOnNhd ℂ (transform S a hS A R hA hR ha hr spectral) {z : ℂ | 0 < z.im} := by
  apply AnalyticOnNhd.pi
  intro i
  simpa only [transform_inner] using
    (data S a hS A R hA hR ha hr spectral i).scalar_analytic (TreeModel.delta S i)

theorem canonical_analytic :
    AnalyticOnNhd ℂ (GlobalWellPosedness.solution S a hS) {z : ℂ | 0 < z.im} := by
  intro z hz
  apply (analytic_transform S a hS A R hA hR ha hr spectral z hz).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  exact (canonical_eq S a hS A R hA hR ha hr spectral hw).symm

theorem canonical_norm_le {z : ℂ} (hz : 0 < z.im) (i : ι) :
    ‖GlobalWellPosedness.solution S a hS z i‖ ≤ z.im⁻¹ := by
  rw [canonical_eq S a hS A R hA hR ha hr spectral hz,transform_inner]
  exact (data S a hS A R hA hR ha hr spectral i).unit_scalar_norm_le z hz
    (TreeModel.delta S i) (TreeModel.norm_delta S i)

/-- Spectral support is derived from the actual Jacobi operator norm. -/
theorem canonical_measure (i : ι) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-(A+2*Real.sqrt R)) (A+2*Real.sqrt R))ᶜ = 0 ∧
      Full.Foundations.Represents (fun z => GlobalWellPosedness.solution S a hS z i) μ := by
  obtain ⟨μ,hμ,hs,hrep⟩ := (data S a hS A R hA hR ha hr spectral i).spectral_measure_of_norm_bound
    (TreeModel.delta S i) (TreeModel.norm_delta S i) (A+2*Real.sqrt R)
    (TreeModel.norm_jacobi S a hS A R hA hR ha hr i)
  refine ⟨μ,hμ,hs,?_⟩
  intro z hz
  dsimp only
  rw [canonical_eq S a hS A R hA hR ha hr spectral hz,transform_inner]
  exact hrep z hz

end NonSymmetricDyson.Paper.TreeSolution
