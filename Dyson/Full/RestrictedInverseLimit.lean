import Dyson.Full.RestrictedInverseUniform

/-! Continuity of projected inverses follows from their exact equations and
uniform bounds. It is not part of the external Perron theorem. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.RestrictedInverseUniform
open Singularities
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Exact resolvent identity for inverses on two moving complements. -/
theorem restricted_inverse_difference
    (F K F₀ K₀ : E →L[ℂ] E) (φ φ₀ : E →L[ℂ] ℂ) (r r₀ : E)
    (hK : IsRestrictedInverse F.toLinearMap K.toLinearMap φ.toLinearMap r)
    (hK₀ : IsRestrictedInverse F₀.toLinearMap K₀.toLinearMap φ₀.toLinearMap r₀)
    (v : E) :
    (K-K₀) v=K ((F-F₀) (K₀ v))+φ₀ v • K (r₀-r)-(φ-φ₀) (K₀ v) • r := by
  have he := congrArg K (hK₀.right_inverse v)
  have h₁ := hK.left_inverse (K₀ v)
  change K (K₀ v-F₀ (K₀ v))=K (v-φ₀ v • r₀) at he
  change K (K₀ v-F (K₀ v))=K₀ v-φ (K₀ v) • r at h₁
  simp only [map_sub,map_smul] at he h₁
  have hkill : K r=0 := hK.kill_right
  have hleft : φ₀ (K₀ v)=0 := hK₀.kill_left v
  calc
    (K-K₀) v = ((K (K₀ v)-K (F₀ (K₀ v)))+φ₀ v • K r₀)-
        ((K (K₀ v)-K (F (K₀ v)))+φ (K₀ v) • r) := by
      rw [he,h₁]
      simp
    _ = _ := by
      simp only [ContinuousLinearMap.sub_apply,map_sub,hkill,hleft,sub_zero]
      abel

/-- A uniformly bounded family of exact projected inverses converges to the
center inverse when the matrix, left functional and right vector converge. -/
theorem restricted_inverse_tendsto {X : Type*} (L : Filter X)
    (F K : X → E →L[ℂ] E) (φ : X → E →L[ℂ] ℂ) (r : X → E)
    (F₀ K₀ : E →L[ℂ] E) (φ₀ : E →L[ℂ] ℂ) (r₀ : E)
    (hF : Tendsto F L (𝓝 F₀)) (hφ : Tendsto φ L (𝓝 φ₀))
    (hr : Tendsto r L (𝓝 r₀))
    (hK₀ : IsRestrictedInverse F₀.toLinearMap K₀.toLinearMap φ₀.toLinearMap r₀)
    (hK : ∀ᶠ x in L, IsRestrictedInverse (F x).toLinearMap (K x).toLinearMap
      (φ x).toLinearMap (r x))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ᶠ x in L, ‖K x‖≤M) :
    Tendsto K L (𝓝 K₀) := by
  let R : ℝ := ‖r₀‖+1
  have hR : 0<R := by dsimp [R]; positivity
  have hrbound : ∀ᶠ x in L, ‖r x‖≤R := hr.norm.eventually_le_const (by dsimp [R]; linarith)
  let e : X → ℝ := fun x =>
    M*‖F x-F₀‖*‖K₀‖+‖φ₀‖*M*‖r₀-r x‖+‖φ x-φ₀‖*‖K₀‖*R
  have he : Tendsto e L (𝓝 0) := by
    have h₁ : Tendsto (fun x => ‖F x-F₀‖) L (𝓝 0) := by simpa using (hF.sub_const F₀).norm
    have h₂ : Tendsto (fun x => ‖r₀-r x‖) L (𝓝 0) := by simpa using (tendsto_const_nhds.sub hr : Tendsto (fun x => r₀-r x) L (𝓝 (r₀-r₀))).norm
    have h₃ : Tendsto (fun x => ‖φ x-φ₀‖) L (𝓝 0) := by simpa using (hφ.sub_const φ₀).norm
    simpa [e] using (((h₁.const_mul M).mul_const ‖K₀‖).add
      (h₂.const_mul (‖φ₀‖*M))).add ((h₃.mul_const ‖K₀‖).mul_const R)
  have hn : ∀ᶠ x in L, ‖K x-K₀‖≤e x := by
    filter_upwards [hK,hbound,hrbound] with x hx hmx hrx
    apply ContinuousLinearMap.opNorm_le_bound _ (by dsimp [e]; positivity)
    intro v
    rw [restricted_inverse_difference (F x) (K x) F₀ K₀ (φ x) φ₀ (r x) r₀ hx hK₀]
    have hKv : ‖K₀ v‖≤‖K₀‖*‖v‖ := K₀.le_opNorm v
    have h₁ : ‖K x ((F x-F₀) (K₀ v))‖≤M*‖F x-F₀‖*‖K₀‖*‖v‖ := by
      calc
        _ ≤ ‖K x‖*(‖F x-F₀‖*(‖K₀‖*‖v‖)) :=
          ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (((F x-F₀).le_opNorm _).trans (mul_le_mul_of_nonneg_left hKv (norm_nonneg _))) (norm_nonneg _))
        _ ≤ M*(‖F x-F₀‖*(‖K₀‖*‖v‖)) := by gcongr
        _ = _ := by ring
    have h₂ : ‖φ₀ v • K x (r₀-r x)‖≤‖φ₀‖*M*‖r₀-r x‖*‖v‖ := by
      rw [norm_smul]
      have hk := ((K x).le_opNorm (r₀-r x)).trans
        (mul_le_mul_of_nonneg_right hmx (norm_nonneg _))
      calc
        _ ≤ (‖φ₀‖*‖v‖)*(M*‖r₀-r x‖) :=
          mul_le_mul (φ₀.le_opNorm v) hk (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have h₃ : ‖(φ x-φ₀) (K₀ v) • r x‖≤‖φ x-φ₀‖*‖K₀‖*R*‖v‖ := by
      rw [norm_smul]
      have hp := ((φ x-φ₀).le_opNorm (K₀ v)).trans
        (mul_le_mul_of_nonneg_left hKv (norm_nonneg _))
      calc
        _ ≤ (‖φ x-φ₀‖*(‖K₀‖*‖v‖))*R := mul_le_mul hp hrx (norm_nonneg _) (by positivity)
        _ = _ := by ring
    exact (norm_sub_le _ _).trans ((add_le_add_right (norm_add_le _ _) _).trans
      ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by dsimp [e]; ring)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hn he

end NonSymmetricDyson.Full.RestrictedInverseUniform
