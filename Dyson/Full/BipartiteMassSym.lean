import Dyson.Full.BoundaryMeasure

/-! The ancillary bipartition-cardinality obstruction. For a symmetric
matrix the exact signed Dyson sum identifies a nonzero signed atomic mass
at a constant potential whenever the bipartition sizes differ. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace NonSymmetricDyson.Full.BipartiteMassSym
variable {ι : Type*} [Fintype ι]

def partitionSign (p : ι → Prop) [DecidablePred p] (i : ι) : ℝ :=
  if p i then 1 else -1

theorem sum_partitionSign_eq_card_difference (p : ι → Prop) [DecidablePred p] :
    (∑ i, partitionSign p i) = ((Finset.univ.filter p).card : ℝ) -
      ((Finset.univ.filter (fun i => ¬p i)).card : ℝ) := by
  classical
  simp [partitionSign, Finset.sum_ite, sub_eq_add_neg]

theorem sum_partitionSign_complex (p : ι → Prop) [DecidablePred p] :
    (∑ i, (partitionSign p i : ℂ)) = ((Finset.univ.filter p).card : ℂ) -
      ((Finset.univ.filter (fun i => ¬p i)).card : ℂ) := by
  exact_mod_cast sum_partitionSign_eq_card_difference p

theorem sum_partitionSign_ne_zero (p : ι → Prop) [DecidablePred p]
    (hcard : (Finset.univ.filter p).card ≠ (Finset.univ.filter (fun i => ¬p i)).card) :
    (∑ i, partitionSign p i) ≠ 0 := by
  rw [sum_partitionSign_eq_card_difference, sub_ne_zero]
  exact_mod_cast hcard

/-- A genuine bipartition changes the two signs on each supported edge. -/
theorem partitionSign_flip (p : ι → Prop) [DecidablePred p] {i j : ι}
    (h : p i ↔ ¬p j) : partitionSign p j = -partitionSign p i := by
  by_cases hi : p i
  · have hj := h.mp hi
    simp [partitionSign, hi, hj]
  · have hj : p j := by tauto
    simp [partitionSign, hi, hj]

/-- Cancellation of the interaction term pairs the two orientations of each
symmetric edge and uses only the bipartition sign relation. -/
theorem signed_interaction_zero (S : Matrix ι ι ℝ) (T : ι → ℝ) (m : ι → ℂ)
    (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → T j = -T i) :
    (∑ i, ∑ j, (T i : ℂ) * (S i j : ℂ) * m i * m j) = 0 := by
  have heq : (∑ i, ∑ j, (T i : ℂ) * (S i j : ℂ) * m i * m j) =
      -(∑ i, ∑ j, (T i : ℂ) * (S i j : ℂ) * m i * m j) := by
    calc
      _ = ∑ j, ∑ i, (T i : ℂ) * (S i j : ℂ) * m i * m j := Finset.sum_comm
      _ = ∑ i, ∑ j, -((T i : ℂ) * (S i j : ℂ) * m i * m j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        by_cases hs : S i j = 0
        · simp [hsym j i, hs]
        · rw [hsym j i, hflip i j hs]
          push_cast
          ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linear_combination (1 / 2 : ℂ) * heq

/-- The exact signed sum for any solution with constant potential. -/
theorem signed_dyson_sum (S : Matrix ι ι ℝ) (T : ι → ℝ) (c : ℝ)
    (z : ℂ) (m : ι → ℂ)
    (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → T j = -T i)
    (hm : ∀ i, m i ≠ 0)
    (heq : BasicEstimates.IsDysonSolution S (fun _ => c) z m) :
    (z - (c : ℂ)) * (∑ i, (T i : ℂ) * m i) = -(∑ i, (T i : ℂ)) := by
  have hi (i : ι) : -(T i : ℂ) = (z - (c : ℂ)) * ((T i : ℂ) * m i) +
      ∑ j, (T i : ℂ) * (S i j : ℂ) * m i * m j := by
    have h := congrArg (fun w : ℂ => (T i : ℂ) * m i * w) (heq i)
    simp only [mul_add, mul_neg, mul_inv_cancel_right₀ (hm i)] at h
    rw [Finset.mul_sum] at h
    convert h using 1 <;> ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hi i)
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    signed_interaction_zero S T m hsym hflip, add_zero] at hsum
  exact hsum.symm

theorem signed_scaled_imaginary (S : Matrix ι ι ℝ) (T : ι → ℝ) (c η : ℝ)
    (m : ι → ℂ) (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → T j = -T i)
    (hm : ∀ i, m i ≠ 0)
    (heq : BasicEstimates.IsDysonSolution S (fun _ => c) (Foundations.vertical c η) m) :
    (∑ i, T i * (η * (m i).im)) = ∑ i, T i := by
  have h := congrArg Complex.re (signed_dyson_sum S T c _ m hsym hflip hm heq)
  simp only [Foundations.vertical, add_sub_cancel_left, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self,
    zero_sub, Complex.re_sum, Complex.im_sum, Complex.neg_re, Complex.mul_im, zero_mul, add_zero] at h
  have he : (∑ i, T i * (η * (m i).im)) = η * ∑ i, T i * (m i).im := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linear_combination -h

/-- The exact signed atom identity, using the general scalar atom formula. -/
theorem signed_atomic_mass (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (T : ι → ℝ) (c : ℝ)
    (m : ℂ → ι → ℂ) (μ : ι → Measure ℝ)
    (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → T j = -T i)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => c) z (m z))
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i)) :
    (∑ i, T i * (μ i {c}).toReal) = ∑ i, T i := by
  have ht : Tendsto (fun η : ℝ => ∑ i, T i * (η * (m (Foundations.vertical c η) i).im))
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ i, T i * (μ i {c}).toReal)) := by
    apply tendsto_finset_sum
    intro i _
    exact (inversion.atom_formula (μ i) (fun z => m z i) c (hμ i) (hrep i)).const_mul (T i)
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hz : 0 < (Foundations.vertical c η).im := by simpa using hη
  exact (signed_scaled_imaginary S T c η _ hsym hflip
    (fun i => BasicEstimates.component_ne_zero (hupper _ hz) i) (heq _ hz)).symm

/-- Unequal signed cardinality forces an actual atom in at least one coordinate. -/
theorem exists_atom_of_sum_ne_zero (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (T : ι → ℝ) (c : ℝ)
    (m : ℂ → ι → ℂ) (μ : ι → Measure ℝ)
    (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → T j = -T i)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => c) z (m z))
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i))
    (hT : (∑ i, T i) ≠ 0) : ∃ i, μ i {c} ≠ 0 := by
  by_contra h
  push_neg at h
  have hm := signed_atomic_mass inversion S T c m μ hsym hflip hupper heq hμ hrep
  simp only [h, ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero] at hm
  exact hT hm.symm

/-- Cardinality formulation, including explicit vertical divergence. -/
theorem unequal_parts_force_atom (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (p : ι → Prop) [DecidablePred p] (c : ℝ)
    (m : ℂ → ι → ℂ) (μ : ι → Measure ℝ)
    (hsym : ∀ i j, S i j = S j i)
    (hflip : ∀ i j, S i j ≠ 0 → partitionSign p j = -partitionSign p i)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution S (fun _ => c) z (m z))
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hrep : ∀ i, Foundations.Represents (fun z => m z i) (μ i))
    (hcard : (Finset.univ.filter p).card ≠ (Finset.univ.filter (fun i => ¬p i)).card) :
    ∃ i, μ i {c} ≠ 0 ∧
      Tendsto (fun η : ℝ => (m (Foundations.vertical c η) i).im) (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨i, hi⟩ := exists_atom_of_sum_ne_zero inversion S (partitionSign p) c m μ
    hsym hflip hupper heq hμ hrep (sum_partitionSign_ne_zero p hcard)
  exact ⟨i, hi, BoundaryMeasure.imaginary_tendsto_atTop_of_atom inversion (μ i)
    (fun z => m z i) c (hμ i) (hrep i) hi⟩

/-- Direct statement for the actual canonical solution. Neither a boundary
value nor a pre-existing atom is assumed. -/
theorem canonical_unequal_parts_force_atom [Nonempty ι]
    (external : Foundations.ExternalStieltjesTheory ι)
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (S : Matrix ι ι ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (hsym : ∀ i j, S i j = S j i)
    (p : ι → Prop) [DecidablePred p]
    (hpart : ∀ i j, S i j ≠ 0 → (p i ↔ ¬p j)) (c : ℝ)
    (hcard : (Finset.univ.filter p).card ≠ (Finset.univ.filter (fun i => ¬p i)).card) :
    let m := GlobalWellPosedness.solution S (fun _ => c) hS
    ∃ μ : ι → Measure ℝ,
      (∀ i, IsProbabilityMeasure (μ i) ∧ Foundations.Represents (fun z => m z i) (μ i)) ∧
      ∃ i, μ i {c} ≠ 0 ∧
        Tendsto (fun η : ℝ => (m (Foundations.vertical c η) i).im)
          (𝓝[>] (0 : ℝ)) atTop := by
  dsimp only
  obtain ⟨_, _, _, μ, hμ⟩ := Foundations.main_theorem_one_max_norm external (fun _ => c) hS
  refine ⟨μ, fun i => ⟨(hμ i).1, (hμ i).2.1⟩, ?_⟩
  exact unequal_parts_force_atom inversion S p c _ μ hsym
    (fun i j h => partitionSign_flip p (hpart i j h))
    (fun z hz => GlobalWellPosedness.solution_upper _ hS hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ hS hz)
    (fun i => (hμ i).1) (fun i => (hμ i).2.1) hcard

end NonSymmetricDyson.Full.BipartiteMassSym
