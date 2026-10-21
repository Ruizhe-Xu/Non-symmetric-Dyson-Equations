import Dyson.Full.Deflation
import Dyson.Full.Singularities

/-! Uniform complementary coercivity and projected inverse bounds for moving
simple eigenspaces. The estimates are derived from finite-dimensional
injectivity and continuity; no uniform inverse bound is an external premise. -/
noncomputable section
open Filter
open scoped Topology
namespace NonSymmetricDyson.Full.RestrictedInverseUniform
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {T : Type*} [TopologicalSpace T]

/-- A moving left eigenspace has a uniform complementary coercivity estimate
near a simple zero eigenvalue. -/
theorem local_complement_coercivity (t₀ : T)
    (B : T → E →L[ℂ] E) (φ : T → E →L[ℂ] ℂ) (r₀ : E)
    (hB : ContinuousAt B t₀) (hφ : ContinuousAt φ t₀)
    (hopen : φ t₀ r₀ ≠ 0)
    (hsimple : ∀ x, B t₀ x = 0 → ∃ c : ℂ, x = c • r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, ∀ x, φ t x = 0 →
      ‖x‖ ≤ C * ‖B t x‖ := by
  obtain ⟨C,hC,hbound⟩ := Deflation.local_augmented_bound t₀ B φ r₀ hB hφ hopen hsimple
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with t ht
  intro x hx
  simpa [hx] using ht x

/-- Uniform norm bound for any actual projected inverse satisfying its two
algebraic identities. Continuity of the projected inverse is not assumed. -/
theorem local_projected_inverse_bound (t₀ : T)
    (B K : T → E →L[ℂ] E) (φ : T → E →L[ℂ] ℂ) (r : T → E)
    (hB : ContinuousAt B t₀) (hφ : ContinuousAt φ t₀) (hr : ContinuousAt r t₀)
    (hopen : φ t₀ (r t₀) ≠ 0)
    (hsimple : ∀ x, B t₀ x = 0 → ∃ c : ℂ, x = c • r t₀)
    (hK : ∀ᶠ t in 𝓝 t₀, ∀ x, φ t (K t x) = 0 ∧ B t (K t x) = x-φ t x • r t) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, ‖K t‖ ≤ C := by
  obtain ⟨A,hA,hcoerce⟩ := local_complement_coercivity t₀ B φ (r t₀) hB hφ hopen hsimple
  let P : ℝ := ‖φ t₀‖+1
  let R : ℝ := ‖r t₀‖+1
  have hP : 0 < P := by dsimp [P]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hp : ∀ᶠ t in 𝓝 t₀, ‖φ t‖ ≤ P := hφ.norm.tendsto.eventually_le_const (by dsimp [P]; linarith)
  have hr' : ∀ᶠ t in 𝓝 t₀, ‖r t‖ ≤ R := hr.norm.tendsto.eventually_le_const (by dsimp [R]; linarith)
  refine ⟨A*(1+P*R),by positivity,?_⟩
  filter_upwards [hcoerce,hK,hp,hr'] with t ht hkt hpt hrt
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  obtain ⟨hkleft,hkright⟩ := hkt x
  have hphix : ‖φ t x‖ ≤ P*‖x‖ :=
    ((φ t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hpt (norm_nonneg _))
  have hproj : ‖x-φ t x • r t‖ ≤ (1+P*R)*‖x‖ := by
    calc
      _ ≤ ‖x‖+‖φ t x • r t‖ := norm_sub_le _ _
      _ = ‖x‖+‖φ t x‖*‖r t‖ := by rw [norm_smul]
      _ ≤ ‖x‖+(P*‖x‖)*R := add_le_add_left
        (mul_le_mul hphix hrt (norm_nonneg _) (by positivity)) _
      _ = _ := by ring
  have hh := ht (K t x) hkleft
  rw [hkright] at hh
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproj hA.le)

/-- The uniform estimate applies in particular to the actual Perron restricted
inverse of I−F, using only its verified algebraic identities. -/
theorem local_perron_restricted_inverse_bound (t₀ : T)
    (F K : T → E →L[ℂ] E) (φ : T → E →L[ℂ] ℂ) (r : T → E)
    (hF : ContinuousAt F t₀) (hφ : ContinuousAt φ t₀) (hr : ContinuousAt r t₀)
    (hnorm : φ t₀ (r t₀) = 1)
    (hsimple : ∀ x, F t₀ x = x → x = φ t₀ x • r t₀)
    (hK : ∀ᶠ t in 𝓝 t₀, Singularities.IsRestrictedInverse
      (F t).toLinearMap (K t).toLinearMap (φ t).toLinearMap (r t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, ‖K t‖ ≤ C := by
  apply local_projected_inverse_bound t₀ (fun t => ContinuousLinearMap.id ℂ E-F t) K φ r
    (continuousAt_const.sub hF) hφ hr (by rw [hnorm]; exact one_ne_zero)
  · intro x hx
    have hfix : F t₀ x=x := by
      change x-F t₀ x=0 at hx
      exact (sub_eq_zero.mp hx).symm
    exact ⟨φ t₀ x,hsimple x hfix⟩
  · filter_upwards [hK] with t ht
    intro x
    exact ⟨ht.kill_left x,ht.right_inverse x⟩

/-- The same coercivity theorem along an arbitrary parameter filter. -/
theorem filter_complement_coercivity {X : Type*} (L : Filter X)
    (B : X → E →L[ℂ] E) (φ : X → E →L[ℂ] ℂ)
    (B₀ : E →L[ℂ] E) (φ₀ : E →L[ℂ] ℂ) (r₀ : E)
    (hB : Tendsto B L (𝓝 B₀)) (hφ : Tendsto φ L (𝓝 φ₀))
    (hopen : φ₀ r₀ ≠ 0)
    (hsimple : ∀ x, B₀ x=0 → ∃ c : ℂ, x=c • r₀) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ t in L, ∀ x, φ t x=0 → ‖x‖≤C*‖B t x‖ := by
  obtain ⟨C,hC,hc⟩ := local_complement_coercivity (B₀,φ₀)
    Prod.fst Prod.snd r₀ continuousAt_fst continuousAt_snd hopen hsimple
  exact ⟨C,hC,(hB.prodMk_nhds hφ).eventually hc⟩

/-- A projected inverse is uniformly bounded along a filter, without
assuming any continuity of that inverse. -/
theorem filter_projected_inverse_bound {X : Type*} (L : Filter X)
    (B K : X → E →L[ℂ] E) (φ : X → E →L[ℂ] ℂ) (r : X → E)
    (B₀ : E →L[ℂ] E) (φ₀ : E →L[ℂ] ℂ) (r₀ : E)
    (hB : Tendsto B L (𝓝 B₀)) (hφ : Tendsto φ L (𝓝 φ₀))
    (hr : Tendsto r L (𝓝 r₀)) (hopen : φ₀ r₀ ≠ 0)
    (hsimple : ∀ x, B₀ x=0 → ∃ c : ℂ, x=c • r₀)
    (hK : ∀ᶠ t in L, ∀ x, φ t (K t x)=0 ∧ B t (K t x)=x-φ t x • r t) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ t in L, ‖K t‖≤C := by
  obtain ⟨A,hA,hcoerce⟩ := filter_complement_coercivity L B φ B₀ φ₀ r₀ hB hφ hopen hsimple
  let P : ℝ := ‖φ₀‖+1
  let R : ℝ := ‖r₀‖+1
  have hP : 0<P := by dsimp [P]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hp : ∀ᶠ t in L, ‖φ t‖≤P := hφ.norm.eventually_le_const (by dsimp [P]; linarith)
  have hr' : ∀ᶠ t in L, ‖r t‖≤R := hr.norm.eventually_le_const (by dsimp [R]; linarith)
  refine ⟨A*(1+P*R),by positivity,?_⟩
  filter_upwards [hcoerce,hK,hp,hr'] with t ht hkt hpt hrt
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  obtain ⟨hkleft,hkright⟩ := hkt x
  have hphix : ‖φ t x‖≤P*‖x‖ :=
    ((φ t).le_opNorm x).trans (mul_le_mul_of_nonneg_right hpt (norm_nonneg _))
  have hproj : ‖x-φ t x • r t‖≤(1+P*R)*‖x‖ := by
    calc
      _ ≤ ‖x‖+‖φ t x • r t‖ := norm_sub_le _ _
      _ = ‖x‖+‖φ t x‖*‖r t‖ := by rw [norm_smul]
      _ ≤ ‖x‖+(P*‖x‖)*R := add_le_add_left
        (mul_le_mul hphix hrt (norm_nonneg _) (by positivity)) _
      _ = _ := by ring
  have hh := ht (K t x) hkleft
  rw [hkright] at hh
  exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproj hA.le)

end NonSymmetricDyson.Full.RestrictedInverseUniform
