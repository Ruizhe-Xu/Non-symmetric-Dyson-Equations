import Mathlib

/-! Quantitative finite-defect absorption. These are general operator lemmas,
proved here rather than assumed as a Dyson stability theorem. -/

noncomputable section

namespace NonSymmetricDyson.Full.Deflation

open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A moving almost-null vector with an exact linear opening gives an inverse
bound of order |z|⁻¹. No differentiability of the vector family is required. -/
theorem linear_opening_bound
    (L L₀ : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) (v b : E) (z : ℂ)
    (K P V B b₀ δ : ℝ)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (hb₀ : 0 < b₀) (hδ : 0 ≤ δ) (hz : z ≠ 0) (hzle : ‖z‖ ≤ 1)
    (hφ : ‖φ‖ ≤ P) (hv : ‖v‖ ≤ V) (hb : ‖b‖ ≤ B)
    (hφv : φ v = 1) (hφb : b₀ ≤ ‖φ b‖)
    (hleft : ∀ x, φ (L₀ x) = 0)
    (hstable : ∀ x, φ x = 0 → ‖x‖ ≤ K * ‖L₀ x‖)
    (hclose : ∀ x, ‖L x - L₀ x‖ ≤ δ * ‖x‖)
    (hopening : L v = z • b)
    (hsmall₁ : K * δ ≤ 1/2) (hsmall₂ : 2 * P * K * δ * B ≤ b₀/2)
    (u : E) :
    ‖u‖ ≤ ((V * (4*P/b₀) + 2*K*(1+B*(4*P/b₀))) / ‖z‖) * ‖L u‖ := by
  let α : ℂ := φ u
  let w : E := u - α • v
  let A : ℝ := ‖α * z‖
  let F : ℝ := ‖L u‖
  have hA : 0 ≤ A := norm_nonneg _
  have hF : 0 ≤ F := norm_nonneg _
  have hw : φ w = 0 := by simp [w, α, hφv]
  have hLw : L w = L u - (α*z) • b := by
    simp [w, hopening, smul_smul]
  have hLwnorm : ‖L w‖ ≤ F + A*B := by
    rw [hLw]
    exact (norm_sub_le _ _).trans (add_le_add_left
      (by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hb hA) F)
  have hL₀ : ‖L₀ w‖ ≤ F + A*B + δ*‖w‖ := by
    have hdecomp : L₀ w = L w - (L w - L₀ w) := by abel
    rw [hdecomp]
    exact (norm_sub_le _ _).trans (add_le_add hLwnorm (hclose w))
  have hW : ‖w‖ ≤ 2*K*(F+A*B) := by
    have hs := (hstable w hw).trans (mul_le_mul_of_nonneg_left hL₀ hK)
    have hss := mul_le_mul_of_nonneg_right hsmall₁ (norm_nonneg w)
    nlinarith
  have hφLw : ‖φ (L w)‖ ≤ P*δ*‖w‖ := by
    have heq : φ (L w) = φ (L w - L₀ w) := by simp [hleft]
    rw [heq]
    calc
      ‖φ (L w - L₀ w)‖ ≤ ‖φ‖ * ‖L w - L₀ w‖ := φ.le_opNorm _
      _ ≤ P * (δ*‖w‖) := mul_le_mul hφ (hclose w) (norm_nonneg _) hP
      _ = _ := by ring
  have hφLu : ‖φ (L u)‖ ≤ P*F :=
    (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hφ hF)
  have hscalar : A*b₀ ≤ P*F + P*δ*‖w‖ := by
    have heq : (α*z) * φ b = φ (L u) - φ (L w) := by
      rw [hLw, map_sub, map_smul]
      simp only [smul_eq_mul]
      ring
    calc
      A*b₀ ≤ A*‖φ b‖ := mul_le_mul_of_nonneg_left hφb hA
      _ = ‖(α*z)*φ b‖ := (norm_mul _ _).symm
      _ = ‖φ (L u) - φ (L w)‖ := by rw [heq]
      _ ≤ ‖φ (L u)‖ + ‖φ (L w)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hφLu hφLw
  have hscalar' : A*b₀ ≤ 2*P*F + (b₀/2)*A := by
    have hh := hscalar.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left hW (mul_nonneg hP hδ)) (P*F))
    have hs₁ := mul_le_mul_of_nonneg_right hsmall₁ (show 0 ≤ 2*P*F by positivity)
    have hs₂ := mul_le_mul_of_nonneg_right hsmall₂ hA
    nlinarith
  have hAbound : A ≤ (4*P/b₀)*F := by
    calc
      A ≤ (4*P*F)/b₀ := (le_div_iff₀ hb₀).mpr (by nlinarith)
      _ = _ := by ring
  have hWbound : ‖w‖ ≤ 2*K*(1+B*(4*P/b₀))*F := by
    calc
      ‖w‖ ≤ 2*K*(F+A*B) := hW
      _ ≤ 2*K*(F+((4*P/b₀)*F)*B) := mul_le_mul_of_nonneg_left
        (add_le_add_left (mul_le_mul_of_nonneg_right hAbound hB) F) (by positivity)
      _ = _ := by ring
  have hdecomp : u = α • v + w := by dsimp [w]; abel
  have hunorm : ‖u‖ ≤ ‖α‖*V + ‖w‖ := by
    calc
      ‖u‖ = ‖α • v + w‖ := by rw [← hdecomp]
      _ ≤ ‖α • v‖ + ‖w‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul]
        exact add_le_add_right (mul_le_mul_of_nonneg_left hv (norm_nonneg α)) _
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmul : ‖u‖*‖z‖ ≤
      (V*(4*P/b₀)+2*K*(1+B*(4*P/b₀)))*F := by
    have hh := mul_le_mul_of_nonneg_right hunorm hzn.le
    have hWz := mul_le_mul_of_nonneg_left hzle (norm_nonneg w)
    have hAV := mul_le_mul_of_nonneg_right hAbound hV
    have hAnorm : A = ‖α‖*‖z‖ := norm_mul _ _
    nlinarith
  calc
    ‖u‖ ≤ ((V*(4*P/b₀)+2*K*(1+B*(4*P/b₀)))*F) / ‖z‖ :=
      (le_div_iff₀ hzn).mpr hmul
    _ = _ := by dsimp [F]; ring

/-- Kernel simplicity constructs a bounded inverse on the fixed complement. -/
theorem complementary_bound_exists [FiniteDimensional ℂ E]
    (L : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) (r : E)
    (hnorm : φ r = 1) (hleft : ∀ x, φ (L x) = 0)
    (hsimple : ∀ x, L x = 0 → x = φ x • r) :
    ∃ K : ℝ, 0 < K ∧ ∀ x, φ x = 0 → ‖x‖ ≤ K * ‖L x‖ := by
  let A : E →L[ℂ] E := L + φ.smulRight r
  have hAx (x : E) : A x = L x + φ x • r := rfl
  have hφA (x : E) : φ (A x) = φ x := by simp [hAx, hleft, hnorm]
  have hinj : Function.Injective A.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change A x = 0 at hx
    have hφx : φ x = 0 := by rw [← hφA x, hx, map_zero]
    have hLx : L x = 0 := by simpa [hAx, hφx] using hx
    simpa [hφx] using hsimple x hLx
  let e : E ≃L[ℂ] E := (LinearEquiv.ofBijective A.toLinearMap
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  refine ⟨1 + ‖e.symm.toContinuousLinearMap‖, by positivity, ?_⟩
  intro x hx
  have he : e x = L x := by change A x = L x; simp [hAx, hx]
  have hid : e.symm (L x) = x := by rw [← he, e.symm_apply_apply]
  calc
    ‖x‖ = ‖e.symm (L x)‖ := congrArg norm hid.symm
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖L x‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := by nlinarith [norm_nonneg (L x)]

/-- Uniform local form of the linear opening argument. Ordinary continuity
and a simple kernel suffice; no Taylor expansion of the operator is assumed. -/
theorem local_linear_opening_bound [FiniteDimensional ℂ E]
    {T : Type*} [TopologicalSpace T] (t₀ : T)
    (L : T → E →L[ℂ] E) (v b : T → E) (φ : E →L[ℂ] ℂ)
    (hL : ContinuousAt L t₀) (hv : ContinuousAt v t₀) (hb : ContinuousAt b t₀)
    (hnorm : φ (v t₀) = 1) (hopen : φ (b t₀) ≠ 0)
    (hleft : ∀ x, φ (L t₀ x) = 0)
    (hsimple : ∀ x, L t₀ x = 0 → x = φ x • v t₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀, ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      L t (v t) = z • b t → ∀ u, ‖u‖ ≤ (C/‖z‖) * ‖L t u‖ := by
  obtain ⟨K, hK, hstable⟩ := complementary_bound_exists (L t₀) φ (v t₀) hnorm hleft hsimple
  let vn : T → E := fun t => (φ (v t))⁻¹ • v t
  let bn : T → E := fun t => (φ (v t))⁻¹ • b t
  have hvn₀ : vn t₀ = v t₀ := by simp [vn, hnorm]
  have hbn₀ : bn t₀ = b t₀ := by simp [bn, hnorm]
  have hφv := φ.continuous.continuousAt.comp hv
  have hφvne : φ (v t₀) ≠ 0 := by rw [hnorm]; norm_num
  have hvn : ContinuousAt vn t₀ := (hφv.inv₀ hφvne).smul hv
  have hbn : ContinuousAt bn t₀ := (hφv.inv₀ hφvne).smul hb
  let P := 1 + ‖φ‖
  let V := 1 + ‖v t₀‖
  let B := 1 + ‖b t₀‖
  let b₀ := ‖φ (b t₀)‖ / 2
  have hP : 0 < P := by dsimp [P]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hb₀ : 0 < b₀ := div_pos (norm_pos_iff.mpr hopen) (by norm_num)
  let δ := min ((2*K)⁻¹) (b₀/(4*P*K*B))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hs₁ : K*δ ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left (2*K)⁻¹ (b₀/(4*P*K*B))) hK.le
    have heq : K*(2*K)⁻¹ = 1/2 := by field_simp
    simpa only [heq] using hh
  have hs₂ : 2*P*K*δ*B ≤ b₀/2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (2*K)⁻¹ (b₀/(4*P*K*B)))
      (show 0 ≤ 2*P*K*B by positivity)
    have heq : (2*P*K*B)*(b₀/(4*P*K*B)) = b₀/2 := by field_simp; ring
    rw [heq] at hh
    convert hh using 1 <;> ring
  have ev : ∀ᶠ t in 𝓝 t₀, ‖vn t‖ ≤ V := hvn.norm.tendsto.eventually_le_const
    (by rw [hvn₀]; dsimp [V]; linarith)
  have eb : ∀ᶠ t in 𝓝 t₀, ‖bn t‖ ≤ B := hbn.norm.tendsto.eventually_le_const
    (by rw [hbn₀]; dsimp [B]; linarith)
  have eo : ∀ᶠ t in 𝓝 t₀, b₀ ≤ ‖φ (bn t)‖ :=
    (φ.continuous.continuousAt.comp hbn).norm.tendsto.eventually_const_le
      (by simp only [Function.comp_apply, hbn₀]; dsimp [b₀]; linarith [norm_pos_iff.mpr hopen])
  have ed : ∀ᶠ t in 𝓝 t₀, ‖L t - L t₀‖ ≤ δ :=
    (hL.sub continuousAt_const).norm.tendsto.eventually_le_const (by simpa using hδ)
  have en : ∀ᶠ t in 𝓝 t₀, φ (v t) ≠ 0 := hφv.eventually_ne hφvne
  let C := V*(4*P/b₀)+2*K*(1+B*(4*P/b₀))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [ev, eb, eo, ed, en] with t hvt hbt hot hdt hnt
  intro z hz hzn heq u
  have hnormt : φ (vn t) = 1 := by simp [vn, hnt]
  have hopening : L t (vn t) = z • bn t := by
    simp only [vn, bn, map_smul, heq, smul_smul]
    congr 1
    ring
  have hclose : ∀ x, ‖L t x - L t₀ x‖ ≤ δ*‖x‖ := by
    intro x
    exact ((L t - L t₀).le_opNorm x).trans (mul_le_mul_of_nonneg_right hdt (norm_nonneg x))
  exact linear_opening_bound (L t) (L t₀) φ (vn t) (bn t) z K P V B b₀ δ
    hK.le hP.le hV.le hB.le hb₀ hδ.le hz hzn
    (by dsimp [P]; linarith) hvt hbt hnormt hot hleft hstable hclose hopening hs₁ hs₂ u

/-- A scalar functional detecting the only kernel direction repairs
coercivity. This is the linear input used for the nonlinear vertex balance. -/
theorem augmented_bound_exists [FiniteDimensional ℂ E]
    (L : E →L[ℂ] E) (ψ : E →L[ℂ] ℂ) (r : E)
    (hopen : ψ r ≠ 0)
    (hsimple : ∀ x, L x = 0 → ∃ c : ℂ, x = c • r) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * (‖L x‖ + ‖ψ x‖) := by
  let A : E →L[ℂ] E × ℂ := L.prod ψ
  have hinj : Function.Injective A.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hLx : L x = 0 := congrArg Prod.fst hx
    have hψx : ψ x = 0 := congrArg Prod.snd hx
    obtain ⟨c, rfl⟩ := hsimple x hLx
    rw [map_smul, smul_eq_mul] at hψx
    have hc : c = 0 := (mul_eq_zero.mp hψx).resolve_right hopen
    simp [hc]
  obtain ⟨C, hC, hbound⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hinj
  refine ⟨(C : ℝ), by exact_mod_cast hC, ?_⟩
  intro x
  have hh : ‖x‖ ≤ (C : ℝ) * ‖A x‖ := by
    simpa using hbound.le_mul_dist x 0
  have hmax : ‖A x‖ ≤ ‖L x‖ + ‖ψ x‖ := by
    change max ‖L x‖ ‖ψ x‖ ≤ _
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  exact hh.trans (mul_le_mul_of_nonneg_left hmax C.coe_nonneg)

/-- The augmented bound persists for nearby operators and functionals. -/
theorem local_augmented_bound [FiniteDimensional ℂ E]
    {T : Type*} [TopologicalSpace T] (t₀ : T)
    (L : T → E →L[ℂ] E) (ψ : T → E →L[ℂ] ℂ) (r : E)
    (hL : ContinuousAt L t₀) (hψ : ContinuousAt ψ t₀)
    (hopen : ψ t₀ r ≠ 0)
    (hsimple : ∀ x, L t₀ x = 0 → ∃ c : ℂ, x = c • r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝 t₀,
      ∀ x, ‖x‖ ≤ C * (‖L t x‖ + ‖ψ t x‖) := by
  obtain ⟨A, hA, hbound⟩ := augmented_bound_exists (L t₀) (ψ t₀) r hopen hsimple
  have he : ∀ᶠ t in 𝓝 t₀, ‖L t - L t₀‖ + ‖ψ t - ψ t₀‖ ≤ (2*A)⁻¹ :=
    ((hL.sub continuousAt_const).norm.add (hψ.sub continuousAt_const).norm).tendsto.eventually_le_const
      (by simp; positivity)
  refine ⟨2*A, by positivity, ?_⟩
  filter_upwards [he] with t ht
  intro x
  have h₁ : ‖L t₀ x‖ ≤ ‖L t x‖ + ‖L t - L t₀‖*‖x‖ := by
    have hh := norm_sub_le (L t x) ((L t - L t₀) x)
    have heq : L t x - (L t - L t₀) x = L t₀ x := by simp
    rw [heq] at hh
    exact hh.trans (add_le_add_left ((L t - L t₀).le_opNorm x) _)
  have h₂ : ‖ψ t₀ x‖ ≤ ‖ψ t x‖ + ‖ψ t - ψ t₀‖*‖x‖ := by
    have hh := norm_sub_le (ψ t x) ((ψ t - ψ t₀) x)
    have heq : ψ t x - (ψ t - ψ t₀) x = ψ t₀ x := by simp
    rw [heq] at hh
    exact hh.trans (add_le_add_left ((ψ t - ψ t₀).le_opNorm x) _)
  have hh := (hbound x).trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hA.le)
  have hs := mul_le_mul_of_nonneg_right ht (show 0 ≤ A*‖x‖ by positivity)
  have hc : (2*A)⁻¹ * (A*‖x‖) = ‖x‖/2 := by field_simp
  rw [hc] at hs
  nlinarith

end NonSymmetricDyson.Full.Deflation
