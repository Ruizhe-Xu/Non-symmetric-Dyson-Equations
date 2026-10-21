import Dyson.Full.BulkMatrixBridge
import Dyson.Full.EuclideanInverse

/-! Exact invariance of the actual Euclidean stability-inverse norm under
finite coordinate permutations. No dimension-dependent norm loss occurs. -/
noncomputable section
namespace NonSymmetricDyson.Full.BulkMatrixBridge
variable {V : Type*} {W : Type*} [Fintype V] [Fintype W]

def euclideanReindex (e : V ≃ W) : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem euclideanReindex_toLp (e : V ≃ W) (v : V → ℂ) :
    euclideanReindex e (WithLp.toLp 2 v)=WithLp.toLp 2 (vector e v) := rfl

theorem stability_inverse_vector_reindex
    (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j,0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (v : V → ℂ) :
    (InteriorStability.stabilityContinuousEquiv
      (S := matrix e S) (a := vector e a) (m := vector e m)
      (fun i j => hS (e.symm i) (e.symm j)) hz
      ((upper_reindex_iff e m).mpr hm) ((dyson_reindex_iff e S a z m).mpr heq)).symm
      (vector e v)=
    vector e ((InteriorStability.stabilityContinuousEquiv hS hz hm heq).symm v) := by
  let E := InteriorStability.stabilityContinuousEquiv hS hz hm heq
  let F := InteriorStability.stabilityContinuousEquiv
    (S := matrix e S) (a := vector e a) (m := vector e m)
    (fun i j => hS (e.symm i) (e.symm j)) hz
    ((upper_reindex_iff e m).mpr hm) ((dyson_reindex_iff e S a z m).mpr heq)
  change F.symm (vector e v)=vector e (E.symm v)
  apply F.injective
  rw [F.apply_symm_apply]
  change vector e v=InteriorStability.stabilityOperator (matrix e S) (vector e m) (vector e (E.symm v))
  rw [stability_reindex]
  have hE : InteriorStability.stabilityOperator S m (E.symm v)=v := E.apply_symm_apply v
  rw [hE]

theorem stability_inverse_euclidean_reindex
    (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j,0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m)
    (v : EuclideanSpace ℂ V) :
    EuclideanInverse.stabilityInverse (matrix e S) (vector e a) z (vector e m)
      (fun i j => hS (e.symm i) (e.symm j)) hz
      ((upper_reindex_iff e m).mpr hm) ((dyson_reindex_iff e S a z m).mpr heq)
      (euclideanReindex e v)=
    euclideanReindex e (EuclideanInverse.stabilityInverse S a z m hS hz hm heq v) := by
  exact congrArg (WithLp.toLp 2)
    (stability_inverse_vector_reindex e S a z m hS hz hm heq (WithLp.ofLp v))

/-- Operator norm is exactly invariant, not merely comparable. -/
theorem stability_inverse_norm_reindex
    (e : V ≃ W) (S : Matrix V V ℝ) (a : V → ℝ) (z : ℂ) (m : V → ℂ)
    (hS : ∀ i j,0≤S i j) (hz : 0<z.im)
    (hm : BasicEstimates.IsUpperSolution m) (heq : BasicEstimates.IsDysonSolution S a z m) :
    ‖EuclideanInverse.stabilityInverse (matrix e S) (vector e a) z (vector e m)
      (fun i j => hS (e.symm i) (e.symm j)) hz
      ((upper_reindex_iff e m).mpr hm) ((dyson_reindex_iff e S a z m).mpr heq)‖=
    ‖EuclideanInverse.stabilityInverse S a z m hS hz hm heq‖ := by
  let A := EuclideanInverse.stabilityInverse S a z m hS hz hm heq
  let B := EuclideanInverse.stabilityInverse (matrix e S) (vector e a) z (vector e m)
    (fun i j => hS (e.symm i) (e.symm j)) hz
    ((upper_reindex_iff e m).mpr hm) ((dyson_reindex_iff e S a z m).mpr heq)
  let P := euclideanReindex e
  have hAB (v) : B (P v)=P (A v) := stability_inverse_euclidean_reindex e S a z m hS hz hm heq v
  change ‖B‖=‖A‖
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have hh := hAB (P.symm v)
    rw [P.apply_symm_apply] at hh
    rw [hh,P.norm_map]
    simpa using A.le_opNorm (P.symm v)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have hh := B.le_opNorm (P v)
    rw [hAB,P.norm_map,P.norm_map] at hh
    exact hh

end NonSymmetricDyson.Full.BulkMatrixBridge
