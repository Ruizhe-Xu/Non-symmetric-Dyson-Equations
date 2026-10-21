import Mathlib

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.Nonlinear

/-- A precise general analytic root-factorization argument. This principle
is independent of Dyson equations: it applies to every analytic two-variable
function with a nondegenerate Newton leading term. It packages the standard
implicit-function, Rouché and removable-singularity arguments. -/
def AnalyticRootFactorizationPrinciple : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (Φ : ℂ × ℂ → ℂ) (γ μ : ℂ),
    AnalyticAt ℂ Φ 0 → γ ≠ 0 → μ ≠ 0 →
    (∃ ε > 0, ∃ B > 0, ∀ θ ω : ℂ, ‖θ‖ < ε → ‖ω‖ < ε →
      ‖Φ (θ, ω) - γ * θ ^ k - μ * ω‖ ≤
        B * (‖θ‖ ^ (k + 1) + ‖θ‖ * ‖ω‖ + ‖ω‖ ^ 2)) →
    ∃ ρ > 0, ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∃ roots : Fin k → ℂ → ℂ,
      (∀ j, ContinuousOn (roots j) {ω | 0 < ω.im ∧ ‖ω‖ < δ}) ∧
      (∀ ω, 0 < ω.im → ‖ω‖ < δ →
        (∀ j, Φ (roots j ω, ω) = 0 ∧
          c * ‖ω‖ ^ ((1 : ℝ) / k) ≤ ‖roots j ω‖ ∧
          ‖roots j ω‖ ≤ C * ‖ω‖ ^ ((1 : ℝ) / k)) ∧
        (∀ i j, i ≠ j → c * ‖ω‖ ^ ((1 : ℝ) / k) ≤ ‖roots i ω - roots j ω‖) ∧
        (∀ θ, ‖θ‖ ≤ ρ →
          c * (∏ j, ‖θ - roots j ω‖) ≤ ‖Φ (θ, ω)‖ ∧
          ‖Φ (θ, ω)‖ ≤ C * (∏ j, ‖θ - roots j ω‖)))

/-- The elementary estimate that makes an approximate root close to at most
one of a separated family of exact roots. -/
theorem separated_root_nearest_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (roots : κ → ℂ) (θ : ℂ) (j₀ : κ) (δ : ℝ)
    (hnearest : ∀ j, ‖θ - roots j₀‖ ≤ ‖θ - roots j‖)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖roots i - roots j‖)
    (j : κ) (hjj : j ≠ j₀) : δ / 2 ≤ ‖θ - roots j‖ := by
  have ht : ‖roots j - roots j₀‖ ≤ ‖θ - roots j‖ + ‖θ - roots j₀‖ := by
    calc
      _ = ‖(roots j - θ) + (θ - roots j₀)‖ := by congr 1; ring
      _ ≤ ‖roots j - θ‖ + ‖θ - roots j₀‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (roots j) θ]
  linarith [hsep j j₀ hjj, hnearest j]

/-- A point cannot lie in two closed root disks when their centers have
a strictly larger separation than twice the radius. -/
theorem disjoint_root_disks
    {κ : Type*} (roots : κ → ℂ) (θ : ℂ) (r δ : ℝ)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖roots i - roots j‖)
    (hr : 2 * r < δ) {i j : κ}
    (hi : ‖θ - roots i‖ ≤ r) (hj : ‖θ - roots j‖ ≤ r) : i = j := by
  by_contra hij
  have ht : ‖roots i - roots j‖ ≤ ‖θ - roots i‖ + ‖θ - roots j‖ := by
    calc
      _ = ‖(roots i - θ) + (θ - roots j)‖ := by congr 1; ring
      _ ≤ ‖roots i - θ‖ + ‖θ - roots j‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev (roots i) θ]
  linarith [hsep i j hij]

/-- The product lower bound and root separation give the linear nearest-root
estimate, with no assertion about which root is selected. -/
theorem nearest_root_product_bound
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (roots : κ → ℂ) (θ : ℂ) (j₀ : κ) (δ c E : ℝ)
    (hδ : 0 < δ) (hc : 0 < c)
    (hnearest : ∀ j, ‖θ - roots j₀‖ ≤ ‖θ - roots j‖)
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖roots i - roots j‖)
    (hproduct : c * (∏ j, ‖θ - roots j‖) ≤ E) :
    ‖θ - roots j₀‖ ≤ E / (c * (δ / 2) ^ (Fintype.card κ - 1)) := by
  have hother : (δ / 2) ^ (Fintype.card κ - 1) ≤
      ∏ j ∈ Finset.univ.erase j₀, ‖θ - roots j‖ := by
    calc
      _ = ∏ _j ∈ Finset.univ.erase j₀, (δ / 2) := by simp [div_pow]
      _ ≤ _ := Finset.prod_le_prod (by intro j _; positivity)
        (fun j hj => separated_root_nearest_bound roots θ j₀ δ hnearest hsep j
          (Finset.mem_erase.mp hj).1)
  have hp : ‖θ - roots j₀‖ * (δ / 2) ^ (Fintype.card κ - 1) ≤
      ∏ j, ‖θ - roots j‖ := by
    calc
      _ ≤ ‖θ - roots j₀‖ * ∏ j ∈ Finset.univ.erase j₀, ‖θ - roots j‖ :=
        mul_le_mul_of_nonneg_left hother (norm_nonneg _)
      _ = _ := Finset.mul_prod_erase Finset.univ (fun j => ‖θ - roots j‖)
        (Finset.mem_univ j₀)
  apply (le_div_iff₀ (by positivity : 0 < c * (δ / 2) ^ (Fintype.card κ - 1))).mpr
  calc
    _ = c * (‖θ - roots j₀‖ * (δ / 2) ^ (Fintype.card κ - 1)) := by ring
    _ ≤ c * (∏ j, ‖θ - roots j‖) := mul_le_mul_of_nonneg_left hp hc.le
    _ ≤ E := hproduct

/-- A finite closed disjoint cover of a connected parameter space cannot
change its label. This proves the continuation step, including zero-radius
disks, directly from connectedness. -/
theorem finite_closed_partition_anchor
    {X κ : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Fintype κ] [DecidableEq κ]
    (s : κ → Set X) (hclosed : ∀ j, IsClosed (s j))
    (hcover : ∀ x, ∃ j, x ∈ s j)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (x₀ : X) (j₀ : κ) (hanchor : x₀ ∈ s j₀) :
    ∀ x, x ∈ s j₀ := by
  have hcompl : (s j₀)ᶜ = ⋃ j : {j : κ // j ≠ j₀}, s j.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hcover x
      have hne : j ≠ j₀ := by intro h; subst j; exact hx hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hne⟩, hj⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      intro hj₀
      exact Set.disjoint_left.mp (hdisjoint j.val j₀ j.property) hj hj₀
  have hcomplclosed : IsClosed (s j₀)ᶜ := by
    rw [hcompl]
    exact isClosed_iUnion_of_finite fun j => hclosed j.val
  have hall : s j₀ = Set.univ :=
    IsClopen.eq_univ ⟨hclosed j₀, isClosed_compl_iff.mp hcomplclosed⟩ ⟨x₀, hanchor⟩
  intro x
  rw [hall]
  trivial

/-- Continuous approximate roots remain in the disk selected by the anchor.
All objects here are actual complex roots and norm distances. -/
theorem continuous_root_disk_selection
    {X κ : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Fintype κ] [DecidableEq κ]
    (roots : κ → X → ℂ) (θ : X → ℂ) (radius separation : X → ℝ)
    (hroots : ∀ j, Continuous (roots j)) (hθ : Continuous θ)
    (hradius : Continuous radius)
    (hsep : ∀ x i j, i ≠ j → separation x ≤ ‖roots i x - roots j x‖)
    (hgap : ∀ x, 2 * radius x < separation x)
    (hnear : ∀ x, ∃ j, ‖θ x - roots j x‖ ≤ radius x)
    (x₀ : X) (j₀ : κ) (hanchor : ‖θ x₀ - roots j₀ x₀‖ ≤ radius x₀) :
    ∀ x, ‖θ x - roots j₀ x‖ ≤ radius x := by
  apply finite_closed_partition_anchor
    (fun j => {x | ‖θ x - roots j x‖ ≤ radius x})
    (fun j => isClosed_le ((hθ.sub (hroots j)).norm) hradius) hnear
    ?_ x₀ j₀ hanchor
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (disjoint_root_disks (fun j => roots j x) (θ x)
    (radius x) (separation x) (hsep x) (hgap x) hi hj)

/-- A continuous exact root has one fixed label among continuous separated
roots. This is proved independently of the approximate-root anchor. -/
theorem continuous_exact_root_selection
    {X κ : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Fintype κ] [DecidableEq κ]
    (roots : κ → X → ℂ) (θ : X → ℂ) (separation : X → ℝ)
    (hroots : ∀ j, Continuous (roots j)) (hθ : Continuous θ)
    (hsep : ∀ x i j, i ≠ j → separation x ≤ ‖roots i x - roots j x‖)
    (hpositive : ∀ x, 0 < separation x)
    (hexact : ∀ x, ∃ j, θ x = roots j x)
    (x₀ : X) (j₀ : κ) (hanchor : θ x₀ = roots j₀ x₀) :
    ∀ x, θ x = roots j₀ x := by
  have h := continuous_root_disk_selection roots θ (fun _ => 0) separation
    hroots hθ continuous_const hsep (by simpa using hpositive)
    (by intro x; obtain ⟨j, hj⟩ := hexact x; exact ⟨j, by simp [hj]⟩)
    x₀ j₀ (by simp [hanchor])
  intro x
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (h x) (norm_nonneg _)))

/-- The physical root is selected from its equation and continuity. The only
anchor supplied here is an ordinary complex distance at one parameter value. -/
theorem anchored_physical_root_bound
    {X κ : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Fintype κ] [DecidableEq κ]
    (roots : κ → X → ℂ) (θg θm : X → ℂ) (radius separation : X → ℝ)
    (hroots : ∀ j, Continuous (roots j)) (hg : Continuous θg) (hm : Continuous θm)
    (hradius : Continuous radius) (hradius0 : ∀ x, 0 ≤ radius x)
    (hsep : ∀ x i j, i ≠ j → separation x ≤ ‖roots i x - roots j x‖)
    (hgap : ∀ x, 2 * radius x < separation x)
    (hnear : ∀ x, ∃ j, ‖θg x - roots j x‖ ≤ radius x)
    (hexact : ∀ x, ∃ j, θm x = roots j x)
    (x₀ : X) (hanchor : ‖θg x₀ - θm x₀‖ ≤ radius x₀) :
    ∀ x, ‖θg x - θm x‖ ≤ radius x := by
  obtain ⟨j₀, hj₀⟩ := hexact x₀
  have hphysical := continuous_exact_root_selection roots θm separation hroots hm hsep
    (fun x => lt_of_le_of_lt (by nlinarith [hradius0 x]) (hgap x)) hexact x₀ j₀ hj₀
  have hselected := continuous_root_disk_selection roots θg radius separation hroots hg
    hradius hsep hgap hnear x₀ j₀ (by simpa only [← hj₀] using hanchor)
  intro x
  simpa only [hphysical x] using hselected x

/-- Reconstruction turns the selected scalar-root distance into the actual
supremum-norm displacement of finite complex vectors. -/
theorem reconstruction_displacement_bound
    {ι : Type*} [Fintype ι]
    (q r mτ g m wg wm : ι → ℂ) (θg θm : ℂ) (L R : ℝ)
    (hg : g = mτ + q * (θg • r + wg))
    (hm : m = mτ + q * (θm • r + wm))
    (hW : ‖wg - wm‖ ≤ L * (‖θg - θm‖ + R)) :
    ‖g - m‖ ≤ ‖q‖ * ((‖r‖ + L) * ‖θg - θm‖ + L * R) := by
  have heq : g - m = q * ((θg - θm) • r + (wg - wm)) := by
    rw [hg, hm]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ‖q‖ * ‖(θg - θm) • r + (wg - wm)‖ := norm_mul_le _ _
    _ ≤ ‖q‖ * (‖(θg - θm) • r‖ + ‖wg - wm‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖q‖ * (‖θg - θm‖ * ‖r‖ + L * (‖θg - θm‖ + R)) := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (add_le_add_left hW _) (norm_nonneg _)
    _ = _ := by ring

/-- A zero of the scalar residual is one of the listed roots, as a direct
consequence of the product lower bound. -/
theorem root_of_product_lower_bound
    {κ : Type*} [Fintype κ] (roots : κ → ℂ) (θ : ℂ) (c : ℝ)
    (hc : 0 < c) (hproduct : c * (∏ j, ‖θ - roots j‖) ≤ 0) :
    ∃ j, θ = roots j := by
  classical
  have hp : ∏ j, ‖θ - roots j‖ = 0 := by
    have hnonneg : 0 ≤ ∏ j, ‖θ - roots j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    nlinarith
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  exact ⟨j, sub_eq_zero.mp (norm_eq_zero.mp hj)⟩

/-- Product factorization and residual control supply the entire disk cover;
connectedness and one anchor then identify its physical component. -/
theorem anchored_product_root_bound
    {X κ : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (roots : κ → X → ℂ) (θg θm : X → ℂ) (Φ : X → ℂ → ℂ)
    (δ : X → ℝ) (c E : ℝ) (hc : 0 < c) (hE : 0 ≤ E)
    (hroots : ∀ j, Continuous (roots j)) (hg : Continuous θg) (hm : Continuous θm)
    (hδ : Continuous δ) (hδpos : ∀ x, 0 < δ x)
    (hsep : ∀ x i j, i ≠ j → δ x ≤ ‖roots i x - roots j x‖)
    (hproductg : ∀ x, c * (∏ j, ‖θg x - roots j x‖) ≤ ‖Φ x (θg x)‖)
    (hproductm : ∀ x, c * (∏ j, ‖θm x - roots j x‖) ≤ ‖Φ x (θm x)‖)
    (hresidual : ∀ x, ‖Φ x (θg x)‖ ≤ E)
    (hphysical : ∀ x, Φ x (θm x) = 0)
    (hsmall : ∀ x, 2 * E < δ x * (c * (δ x / 2) ^ (Fintype.card κ - 1)))
    (x₀ : X)
    (hanchor : ‖θg x₀ - θm x₀‖ ≤ E / (c * (δ x₀ / 2) ^ (Fintype.card κ - 1))) :
    ∀ x, ‖θg x - θm x‖ ≤ E / (c * (δ x / 2) ^ (Fintype.card κ - 1)) := by
  let radius := fun x => E / (c * (δ x / 2) ^ (Fintype.card κ - 1))
  have hden : ∀ x, 0 < c * (δ x / 2) ^ (Fintype.card κ - 1) := by
    intro x
    have hx := hδpos x
    positivity
  have hradius : Continuous radius :=
    continuous_const.div (continuous_const.mul ((hδ.div_const 2).pow _)) (fun x => (hden x).ne')
  have hnear : ∀ x, ∃ j, ‖θg x - roots j x‖ ≤ radius x := by
    intro x
    obtain ⟨j₀, hj₀⟩ := Finite.exists_min (fun j => ‖θg x - roots j x‖)
    exact ⟨j₀, nearest_root_product_bound (fun j => roots j x) (θg x) j₀ (δ x) c E
      (hδpos x) hc hj₀ (hsep x) ((hproductg x).trans (hresidual x))⟩
  have hexact : ∀ x, ∃ j, θm x = roots j x := by
    intro x
    apply root_of_product_lower_bound (fun j => roots j x) (θm x) c hc
    simpa [hphysical x] using hproductm x
  have hgap : ∀ x, 2 * radius x < δ x := by
    intro x
    dsimp [radius]
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ (hden x)).mpr (hsmall x)
  exact anchored_physical_root_bound roots θg θm radius δ hroots hg hm hradius
    (fun x => div_nonneg hE (hden x).le) hsep hgap hnear hexact x₀ hanchor

/-- Reconstruction preserves the fine residual-over-separation estimate.
The denominator restriction is the local bounded spectral neighborhood. -/
theorem fine_reconstruction_displacement_bound
    {ι : Type*} [Fintype ι]
    (q r mτ g m wg wm : ι → ℂ) (θg θm : ℂ) (L A E den : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hE : 0 ≤ E) (hden : 0 < den) (hden1 : den ≤ 1)
    (hg : g = mτ + q * (θg • r + wg))
    (hm : m = mτ + q * (θm • r + wm))
    (hscalar : ‖θg - θm‖ ≤ A * E / den)
    (hW : ‖wg - wm‖ ≤ L * (‖θg - θm‖ + E)) :
    ‖g - m‖ ≤ (‖q‖ * ((‖r‖ + L) * A + L)) * E / den := by
  have hEden : E ≤ E / den := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ ‖q‖ * ((‖r‖ + L) * ‖θg - θm‖ + L * E) :=
      reconstruction_displacement_bound q r mτ g m wg wm θg θm L E hg hm hW
    _ ≤ ‖q‖ * ((‖r‖ + L) * (A * E / den) + L * (E / den)) := by gcongr
    _ = _ := by ring

end NonSymmetricDyson.Full.Nonlinear
