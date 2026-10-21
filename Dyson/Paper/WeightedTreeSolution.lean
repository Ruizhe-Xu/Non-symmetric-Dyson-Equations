import Dyson.Paper.WeightedTreeModel
import Dyson.Paper.TreeSpectral
import Dyson.Paper.Foundations

/-! Root Green functions of the actual signed-weight type-word operators satisfy the
Dyson equation. The only external input is the general bounded self-adjoint
spectral principle; the tree, operators and Schur recurrence are proved. -/
noncomputable section
open scoped BigOperators Topology Classical
open MeasureTheory
namespace NonSymmetricDyson.Paper.WeightedTreeSolution
universe u
variable {ι : Type u} [Fintype ι]
variable (S b : ι → ι → ℝ) (a : ι → ℝ)
variable (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
variable (ha : ∀ i, |a i| ≤ A) (hr : ∀ i, (∑ j : {j : ι // 0 < S i j}, b i j.val ^ 2) ≤ R)
variable (spectral : TreeSpectral.BoundedSelfAdjointSpectralPrinciple.{u})

/-- The finite equation retains squared signed couplings on the permitted transitions. -/
def coefficient (i j : ι) : ℝ := if 0 < S i j then b i j ^ 2 else 0

theorem coefficient_nonnegative : ∀ i j, 0 ≤ coefficient S b i j := by
  intro i j
  unfold coefficient
  split_ifs <;> positivity

def data (i : ι) : TreeSpectral.ResolventMeasureData
    (WeightedTreeModel.jacobi S b a A R hA hR ha hr i) :=
  (spectral _ (WeightedTreeModel.jacobi_selfAdjoint S b a A R hA hR ha hr i)).some

def transform (z : ℂ) (i : ι) : ℂ :=
  WeightedTreeModel.root S i ((data S b a A R hA hR ha hr spectral i).green z (WeightedTreeModel.delta S i))

include A R hA hR ha hr spectral

theorem transform_inner (z : ℂ) (i : ι) :
    transform S b a A R hA hR ha hr spectral z i =
      inner ℂ (WeightedTreeModel.delta S i)
        ((data S b a A R hA hR ha hr spectral i).green z (WeightedTreeModel.delta S i)) :=
  (WeightedTreeModel.inner_delta S i _).symm

theorem transform_upper {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsUpperSolution (transform S b a A R hA hR ha hr spectral z) := by
  intro i
  rw [transform_inner]
  apply TreeSpectral.ResolventMeasureData.scalar_im_pos _ z hz
  intro he
  have hh := WeightedTreeModel.norm_delta S i
  rw [he,norm_zero] at hh
  exact zero_ne_one hh

/-- Root deletion for the concrete tree yields the original finite system. -/
theorem transform_equation {z : ℂ} (hz : 0 < z.im) :
    BasicEstimates.IsDysonSolution (coefficient S b) a z (transform S b a A R hA hR ha hr spectral z) := by
  intro i
  let D := data S b a A R hA hR ha hr spectral
  have hs := TreeSchur.weighted_branch_resolvent_identity
    (WeightedTreeModel.jacobi S b a A R hA hR ha hr i)
    (fun j : TreeWords.Word.Child (.nil i) => WeightedTreeModel.jacobi S b a A R hA hR ha hr j.val)
    (WeightedTreeModel.root S i)
    (fun j => WeightedTreeModel.branch S j.property)
    (fun j => WeightedTreeModel.root S j.val)
    (fun j => WeightedTreeModel.delta S j.val)
    (fun j => b i j.val) (WeightedTreeModel.delta S i) (a i : ℂ) z
    ((D i).shifted z hz) (fun j => (D j.val).shifted z hz)
    ((D i).shifted_apply z hz) (fun j => (D j.val).shifted_apply z hz)
    (WeightedTreeModel.jacobi_root S b a A R hA hR ha hr i)
    (fun j => WeightedTreeModel.jacobi_branch S b a A R hA hR ha hr j.property)
    (WeightedTreeModel.root_delta S i) (fun j => WeightedTreeModel.branch_delta S j.property)
  have hg (j : ι) : (D j).green z = ((D j).shifted z hz).symm.toContinuousLinearMap :=
    (D j).green_eq z hz
  have hm (j : ι) : WeightedTreeModel.root S j (((D j).shifted z hz).symm (WeightedTreeModel.delta S j)) =
      transform S b a A R hA hR ha hr spectral z j := by
    unfold transform
    rw [show (data S b a A R hA hR ha hr spectral j).green z =
      ((D j).shifted z hz).symm.toContinuousLinearMap from hg j]
    rfl
  rw [hm] at hs
  rw [hs.2]
  congr 1
  calc
    _ = ∑ j : {j : ι // 0 < S i j}, (coefficient S b i j.val : ℂ) *
        transform S b a A R hA hR ha hr spectral z j.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hm]
      have hj : 0 < S i j.val := j.property
      simp only [coefficient, if_pos hj]
    _ = _ := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 0 < S i j)
        (fun j => (coefficient S b i j : ℂ) * transform S b a A R hA hR ha hr spectral z j)]
      have he : (∑ j : {j : ι // ¬0 < S i j}, (coefficient S b i j.val : ℂ) *
          transform S b a A R hA hR ha hr spectral z j.val) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        simp [coefficient, j.property]
      rw [he,add_zero]

/-- Existence is obtained from the tree; only the already proved finite
Dyson uniqueness theorem is used to identify any competing solution. -/
theorem wellPosedness : Model.WellPosednessTarget (coefficient S b) a := by
  intro z hz
  refine ⟨transform S b a A R hA hR ha hr spectral z,
    ⟨transform_upper S b a A R hA hR ha hr spectral hz,
      transform_equation S b a A R hA hR ha hr spectral hz⟩,?_⟩
  intro m hm
  exact Uniqueness.upper_half_plane_unique (coefficient_nonnegative S b) hz hm.1
    (transform_upper S b a A R hA hR ha hr spectral hz) hm.2
    (transform_equation S b a A R hA hR ha hr spectral hz)

theorem canonical_eq {z : ℂ} (hz : 0 < z.im) :
    GlobalWellPosedness.solution (coefficient S b) a (coefficient_nonnegative S b) z = transform S b a A R hA hR ha hr spectral z :=
  GlobalWellPosedness.solution_eq_of_upper_solution a (coefficient_nonnegative S b) hz
    (transform_upper S b a A R hA hR ha hr spectral hz)
    (transform_equation S b a A R hA hR ha hr spectral hz)

theorem analytic_transform :
    AnalyticOnNhd ℂ (transform S b a A R hA hR ha hr spectral) {z : ℂ | 0 < z.im} := by
  apply AnalyticOnNhd.pi
  intro i
  simpa only [transform_inner] using
    (data S b a A R hA hR ha hr spectral i).scalar_analytic (WeightedTreeModel.delta S i)

theorem canonical_analytic :
    AnalyticOnNhd ℂ (GlobalWellPosedness.solution (coefficient S b) a (coefficient_nonnegative S b)) {z : ℂ | 0 < z.im} := by
  intro z hz
  apply (analytic_transform S b a A R hA hR ha hr spectral z hz).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  exact (canonical_eq S b a A R hA hR ha hr spectral hw).symm

theorem canonical_norm_le {z : ℂ} (hz : 0 < z.im) (i : ι) :
    ‖GlobalWellPosedness.solution (coefficient S b) a (coefficient_nonnegative S b) z i‖ ≤ z.im⁻¹ := by
  rw [canonical_eq S b a A R hA hR ha hr spectral hz,transform_inner]
  exact (data S b a A R hA hR ha hr spectral i).unit_scalar_norm_le z hz
    (WeightedTreeModel.delta S i) (WeightedTreeModel.norm_delta S i)

/-- Spectral support is derived from the actual Jacobi operator norm. -/
theorem canonical_measure (i : ι) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      μ (Set.Icc (-(A+2*Real.sqrt R)) (A+2*Real.sqrt R))ᶜ = 0 ∧
      Full.Foundations.Represents (fun z => GlobalWellPosedness.solution (coefficient S b) a (coefficient_nonnegative S b) z i) μ := by
  obtain ⟨μ,hμ,hs,hrep⟩ := (data S b a A R hA hR ha hr spectral i).spectral_measure_of_norm_bound
    (WeightedTreeModel.delta S i) (WeightedTreeModel.norm_delta S i) (A+2*Real.sqrt R)
    (WeightedTreeModel.norm_jacobi S b a A R hA hR ha hr i)
  refine ⟨μ,hμ,hs,?_⟩
  intro z hz
  dsimp only
  rw [canonical_eq S b a A R hA hR ha hr spectral hz,transform_inner]
  exact hrep z hz

end NonSymmetricDyson.Paper.WeightedTreeSolution
