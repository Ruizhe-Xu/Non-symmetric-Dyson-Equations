import Dyson.Full.AtomRemoval

/-! The literal dominated-convergence calculation in M2 Step 3 and the
removal of zero-weight terms from the finite list of singular points. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace NonSymmetricDyson.Paper.BoundaryAtoms
open Full Full.Boundary Full.Poisson

/-- The atom formula follows by dominated convergence to the singleton
indicator. It is proved for every finite measure, without Stieltjes inversion. -/
theorem stieltjes_atom_formula (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℝ) :
    Tendsto (fun η : ℝ => η * (Poisson.stieltjes μ (Poisson.point τ η)).im)
      (𝓝[>] 0) (𝓝 ((μ {τ}).toReal)) := by
  classical
  let F : ℝ → ℝ → ℝ := fun η t => η^2 / ((t-τ)^2+η^2)
  let f : ℝ → ℝ := Set.indicator {τ} (fun _ => 1)
  have hηevent : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hmeas : ∀ᶠ η : ℝ in 𝓝[>] 0, AEStronglyMeasurable (F η) μ := by
    filter_upwards [] with η
    exact (measurable_const.div
      (((measurable_id.sub_const τ).pow_const 2).add_const (η^2))).aestronglyMeasurable
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ᵐ t ∂μ, ‖F η t‖ ≤ (1:ℝ) := by
    filter_upwards [hηevent] with η hη
    filter_upwards [] with t
    have hd : 0 < (t-τ)^2+η^2 := by positivity
    dsimp [F]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hd.le)]
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg (t-τ)]
  have hlim : ∀ᵐ t ∂μ, Tendsto (fun η => F η t) (𝓝[>] 0) (𝓝 (f t)) := by
    filter_upwards [] with t
    by_cases ht : t = τ
    · subst t
      have he : (fun η => F η τ) =ᶠ[𝓝[>] (0:ℝ)] (fun _ => 1) := by
        filter_upwards [hηevent] with η hη
        simp [F,ne_of_gt hη]
      simpa [f] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] 0) (𝓝 1)).congr' he.symm
    · have hid : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hden : (t-τ)^2+(0:ℝ)^2 ≠ 0 := by simpa using pow_ne_zero 2 (sub_ne_zero.mpr ht)
      simpa [F,f,ht] using (hid.pow 2).div (tendsto_const_nhds.add (hid.pow 2)) hden
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (f := f) (fun _ => (1:ℝ)) hmeas hbound (integrable_const 1) hlim
  have hi : (∫ t, f t ∂μ) = (μ {τ}).toReal := by
    simp [f, integral_indicator (measurableSet_singleton τ), measureReal_def]
  rw [hi] at hdct
  apply hdct.congr'
  filter_upwards [hηevent] with η hη
  rw [Poisson.stieltjes_im μ τ hη, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [F,Poisson.kernel]
  ring

/-- Transfer of the proved scalar formula to any actual Stieltjes
representation, in the precise vertical convention used in M2. -/
theorem represented_atom_formula (μ : Measure ℝ) (f : ℂ → ℂ) (τ : ℝ)
    (hμ : IsProbabilityMeasure μ) (hrep : Foundations.Represents f μ) :
    Tendsto (fun η : ℝ => η * (f (Foundations.vertical τ η)).im)
      (𝓝[>] 0) (𝓝 ((μ {τ}).toReal)) := by
  letI := hμ
  apply (stieltjes_atom_formula μ τ).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  have he : Poisson.point τ η = Foundations.vertical τ η := by
    apply Complex.ext <;> simp [Poisson.point,Foundations.vertical]
  rw [he, hrep _ (by simpa [Foundations.vertical] using hη)]
  rfl

/-- The paper lists only atoms with positive weight. -/
def positiveAtoms (μ : Measure ℝ) (A : Finset ℝ) : Finset ℝ :=
  A.filter (fun τ => 0 < μ {τ})

theorem positiveAtoms_subset (μ : Measure ℝ) (A : Finset ℝ) :
    positiveAtoms μ A ⊆ A := Finset.filter_subset _ _

theorem positiveAtoms_positive (μ : Measure ℝ) (A : Finset ℝ) {τ : ℝ}
    (h : τ ∈ positiveAtoms μ A) : 0 < μ {τ} := (Finset.mem_filter.mp h).2

/-- Removing zero-weight poles does not change the atom-removed transform. -/
theorem atomRemoved_positiveAtoms (μ : Measure ℝ) (f : ℂ → ℂ) (A : Finset ℝ) :
    atomRemoved μ f (positiveAtoms μ A) = atomRemoved μ f A := by
  classical
  funext z
  unfold atomRemoved positiveAtoms
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs with h
  · rfl
  · have hz : μ {τ} = 0 := le_antisymm (le_of_not_gt h) bot_le
    simp [hz]

/-- The finite atomic measure also ignores precisely the zero-weight terms. -/
theorem atomic_measure_positiveAtoms (μ : Measure ℝ) (A : Finset ℝ) :
    (∑ τ ∈ positiveAtoms μ A, μ {τ} • Measure.dirac τ) =
      ∑ τ ∈ A, μ {τ} • Measure.dirac τ := by
  classical
  unfold positiveAtoms
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs with h
  · rfl
  · have hz : μ {τ} = 0 := le_antisymm (le_of_not_gt h) bot_le
    simp [hz]

end NonSymmetricDyson.Paper.BoundaryAtoms
