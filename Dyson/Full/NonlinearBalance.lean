import Dyson.Full.Nonlinear

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Nonlinear

variable {ι : Type*} [Fintype ι]

/-- Norm estimate for the exact displacement residual, available independently
of whether the linear operator is invertible. -/
theorem residual_action_norm_bound
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (b M : ℝ) (hb : 0 < b) (hM : 0 ≤ M)
    (hm0 : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hlo : ∀ i, b ≤ ‖g i‖) (hhi : ∀ i, ‖m i‖ ≤ M) :
    ‖DysonPaper.Algebra.stabilityAction m (Model.action S) (g - m)‖ ≤
      M ^ 2 * ‖Model.residual S a z g‖ + (1 / b) * ‖g - m‖ ^ 2 := by
  have hg0 : ∀ i, g i ≠ 0 := fun i => norm_pos_iff.mp (hb.trans_le (hlo i))
  rw [Model.exact_residual_expansion S a z m g hsol hm0 hg0]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hsq : ‖m i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (m i), hhi i]
  have hsqU : ‖g i - m i‖ ^ 2 ≤ ‖g - m‖ ^ 2 := by
    have ht := norm_le_pi_norm (g - m) i
    simp only [Pi.sub_apply] at ht
    nlinarith [norm_nonneg (g i - m i)]
  have hquot : ‖g i - m i‖ ^ 2 / ‖g i‖ ≤ (1 / b) * ‖g - m‖ ^ 2 := by
    apply (div_le_iff₀ (hb.trans_le (hlo i))).mpr
    have hden : (1 : ℝ) ≤ (1 / b) * ‖g i‖ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hb).mpr
      nlinarith [hlo i]
    nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg ‖g - m‖)]
  calc
    _ ≤ ‖m i ^ 2 * Model.residual S a z g i‖ + ‖(g i - m i) ^ 2 / g i‖ := norm_add_le _ _
    _ = ‖m i‖ ^ 2 * ‖Model.residual S a z g i‖ + ‖g i - m i‖ ^ 2 / ‖g i‖ := by
      simp only [norm_mul, norm_pow, norm_div]
    _ ≤ _ := add_le_add
      (mul_le_mul hsq (norm_le_pi_norm (Model.residual S a z g) i) (norm_nonneg _) (sq_nonneg M)) hquot

/-- Exact reconstructed vertex balance for an arbitrary finite incidence
operator. The graph-specific incidence matrix is a special case. -/
def vertexBalance {κ : Type*} [Fintype κ]
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T d : κ → ℂ) (u : ι → ℂ) : ℂ :=
  ∑ i, T i * (-(d i + B u i)⁻¹ - (-(d i)⁻¹))

def vertexBalanceLinear {κ : Type*} [Fintype κ]
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T d : κ → ℂ) (u : ι → ℂ) : ℂ :=
  ∑ i, T i * (-(d i)⁻¹) ^ 2 * B u i

/-- All reconstructed vertex denominators and the summed quadratic error
are verified before the balance is used. -/
theorem vertex_balance_remainder_bound
    {κ : Type*} [Fintype κ]
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T d : κ → ℂ) (u : ι → ℂ)
    (V : ℝ) (hV : 0 ≤ V) (hd : ∀ i, d i ≠ 0)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hv : ∀ i, ‖-(d i)⁻¹‖ ≤ V)
    (hsmall : V * ‖B‖ * ‖u‖ ≤ 1 / 2) :
    (∀ i, d i + B u i ≠ 0) ∧
      ‖vertexBalance B T d u - vertexBalanceLinear B T d u‖ ≤
        (2 * Fintype.card κ * V ^ 3 * ‖B‖ ^ 2) * ‖u‖ ^ 2 := by
  have hBu : ∀ i, ‖B u i‖ ≤ ‖B‖ * ‖u‖ := fun i => (norm_le_pi_norm (B u) i).trans (B.le_opNorm u)
  have hrel : ∀ i, ‖(-(d i)⁻¹) * B u i‖ ≤ 1 / 2 := by
    intro i
    rw [norm_mul]
    calc
      _ ≤ V * (‖B‖ * ‖u‖) := mul_le_mul (hv i) (hBu i) (norm_nonneg _) hV
      _ = V * ‖B‖ * ‖u‖ := by ring
      _ ≤ _ := hsmall
  refine ⟨fun i => vertex_denominator_nonzero (d i) (B u i) (hd i) (hrel i), ?_⟩
  have hpoint : ∀ i, ‖T i * (-(d i + B u i)⁻¹ - (-(d i)⁻¹) - (-(d i)⁻¹) ^ 2 * B u i)‖ ≤
      2 * V ^ 3 * ‖B‖ ^ 2 * ‖u‖ ^ 2 := by
    intro i
    rw [norm_mul]
    calc
      _ ≤ 1 * (2 * ‖-(d i)⁻¹‖ ^ 3 * ‖B u i‖ ^ 2) :=
        mul_le_mul (hT i) (vertex_quadratic_remainder (d i) (B u i) (hd i) (hrel i))
          (norm_nonneg _) zero_le_one
      _ ≤ 1 * (2 * V ^ 3 * (‖B‖ * ‖u‖) ^ 2) := by
        gcongr
        · exact hv i
        · exact hBu i
      _ = _ := by ring
  have he : vertexBalance B T d u - vertexBalanceLinear B T d u =
      ∑ i, T i * (-(d i + B u i)⁻¹ - (-(d i)⁻¹) - (-(d i)⁻¹) ^ 2 * B u i) := by
    rw [vertexBalance, vertexBalanceLinear, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, ‖T i * (-(d i + B u i)⁻¹ - (-(d i)⁻¹) - (-(d i)⁻¹) ^ 2 * B u i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : κ, 2 * V ^ 3 * ‖B‖ ^ 2 * ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => hpoint i
    _ = _ := by simp; ring

/-- Nonlinear balance stability follows from a genuine augmented linear
coercivity estimate and the two actual quadratic residual bounds. -/
theorem nonlinear_balance_absorption
    {κ : Type*} [Fintype κ]
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (z : ℂ) (m g : ι → ℂ)
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T d : κ → ℂ)
    (b M V A : ℝ) (hb : 0 < b) (hM : 0 ≤ M) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hm0 : ∀ i, m i ≠ 0) (hsol : BasicEstimates.IsDysonSolution S a z m)
    (hlo : ∀ i, b ≤ ‖g i‖) (hhi : ∀ i, ‖m i‖ ≤ M)
    (hd : ∀ i, d i ≠ 0) (hT : ∀ i, ‖T i‖ ≤ 1) (hv : ∀ i, ‖-(d i)⁻¹‖ ≤ V)
    (hvertexsmall : V * ‖B‖ * ‖g - m‖ ≤ 1 / 2)
    (hlinear : ∀ u, ‖u‖ ≤ A *
      (‖DysonPaper.Algebra.stabilityAction m (Model.action S) u‖ + ‖vertexBalanceLinear B T d u‖))
    (hsmall : A * (1 / b + 2 * Fintype.card κ * V ^ 3 * ‖B‖ ^ 2) * ‖g - m‖ ≤ 1 / 2) :
    (∀ i, d i + B (g - m) i ≠ 0) ∧
      ‖g - m‖ ≤ 2 * A * (M ^ 2 * ‖Model.residual S a z g‖ + ‖vertexBalance B T d (g - m)‖) := by
  obtain ⟨hden, hvertex⟩ := vertex_balance_remainder_bound B T d (g - m) V hV hd hT hv hvertexsmall
  refine ⟨hden, ?_⟩
  have hres := residual_action_norm_bound S a z m g b M hb hM hm0 hsol hlo hhi
  have hbal : ‖vertexBalanceLinear B T d (g - m)‖ ≤ ‖vertexBalance B T d (g - m)‖ +
      (2 * Fintype.card κ * V ^ 3 * ‖B‖ ^ 2) * ‖g - m‖ ^ 2 := by
    have ht : ‖vertexBalanceLinear B T d (g - m)‖ ≤ ‖vertexBalance B T d (g - m)‖ +
        ‖vertexBalance B T d (g - m) - vertexBalanceLinear B T d (g - m)‖ := by
      calc
        _ = ‖vertexBalance B T d (g - m) -
            (vertexBalance B T d (g - m) - vertexBalanceLinear B T d (g - m))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    exact ht.trans (add_le_add_left hvertex _)
  have hineq : ‖g - m‖ ≤
      A * (M ^ 2 * ‖Model.residual S a z g‖ + ‖vertexBalance B T d (g - m)‖) +
      (A * (1 / b + 2 * Fintype.card κ * V ^ 3 * ‖B‖ ^ 2)) * ‖g - m‖ ^ 2 := by
    have hh := (hlinear (g - m)).trans (mul_le_mul_of_nonneg_left (add_le_add hres hbal) hA)
    convert hh using 1 <;> ring
  have h := quadratic_absorption (norm_nonneg (g - m)) (by positivity) (by positivity) hsmall hineq
  convert h using 1 <;> ring

/-- Uniform closeness radius for the augmented nonlinear estimate. The radius
is chosen from the fixed linear and reconstruction constants before `m,g,z`. -/
theorem uniform_nonlinear_balance_radius
    {κ : Type*} [Fintype κ]
    (S : Matrix ι ι ℝ) (a : ι → ℝ)
    (B : (ι → ℂ) →L[ℂ] (κ → ℂ)) (T : κ → ℂ)
    (b M V A : ℝ) (hb : 0 < b) (hM : 0 ≤ M) (hV : 0 ≤ V) (hA : 0 < A)
    (hT : ∀ i, ‖T i‖ ≤ 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z : ℂ) (m g : ι → ℂ) (d : κ → ℂ),
      BasicEstimates.IsDysonSolution S a z m →
      (∀ i, 2 * b ≤ ‖m i‖) → (∀ i, ‖m i‖ ≤ M) →
      (∀ i, d i ≠ 0) → (∀ i, ‖-(d i)⁻¹‖ ≤ V) →
      (∀ u, ‖u‖ ≤ A * (‖DysonPaper.Algebra.stabilityAction m (Model.action S) u‖ +
        ‖vertexBalanceLinear B T d u‖)) →
      ‖g - m‖ ≤ c →
      (∀ i, d i + B (g - m) i ≠ 0) ∧
      ‖g - m‖ ≤ C * (‖Model.residual S a z g‖ + ‖vertexBalance B T d (g - m)‖) := by
  let D := A * (1 / b + 2 * Fintype.card κ * V ^ 3 * ‖B‖ ^ 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let c := min b (min (1 / (2 * (V * ‖B‖ + 1))) (1 / (2 * (D + 1))))
  have hc : 0 < c := lt_min hb (lt_min (by positivity) (by positivity))
  refine ⟨c, 2 * A * (M ^ 2 + 1), hc, by positivity, ?_⟩
  intro z m g d hsol hlo hhi hd hv hlinear hclose
  have hU : 0 ≤ ‖g - m‖ := norm_nonneg _
  have hcloseb : ‖g - m‖ ≤ b := hclose.trans (min_le_left _ _)
  have hglo : ∀ i, b ≤ ‖g i‖ := by
    intro i
    have ht := norm_sub_norm_le (m i) (g i)
    rw [norm_sub_rev] at ht
    have hu := norm_le_pi_norm (g - m) i
    simp only [Pi.sub_apply] at hu
    linarith [hlo i]
  have hvertex : V * ‖B‖ * ‖g - m‖ ≤ 1 / 2 := by
    have hbound := hclose.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (V * ‖B‖ + 1))).mp hbound
    nlinarith
  have hsmall : D * ‖g - m‖ ≤ 1 / 2 := by
    have hbound := hclose.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (D + 1))).mp hbound
    nlinarith
  obtain ⟨hden, hbound⟩ := nonlinear_balance_absorption S a z m g B T d b M V A hb hM hV hA.le
    (fun i => norm_pos_iff.mp (by linarith [hlo i])) hsol hglo hhi hd hT hv hvertex hlinear hsmall
  refine ⟨hden, hbound.trans ?_⟩
  rw [mul_assoc (2 * A) (M ^ 2 + 1)]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * A)
  nlinarith [norm_nonneg (Model.residual S a z g), norm_nonneg (vertexBalance B T d (g - m)),
    mul_nonneg (sq_nonneg M) (norm_nonneg (vertexBalance B T d (g - m)))]

end NonSymmetricDyson.Full.Nonlinear
