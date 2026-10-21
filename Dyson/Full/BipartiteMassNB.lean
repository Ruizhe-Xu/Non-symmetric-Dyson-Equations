import Dyson.Full.BulkNBQuantitative
import Dyson.Full.Origin
import Dyson.Full.BoundaryMeasure
import Dyson.Full.BipartiteMassSym

/-! The unequal-part obstruction for NB uses base vertices, not directed
edges (whose two classes always have equal cardinality). The exact signed
vertex resolvent identity forces an atom of a cavity measure. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace NonSymmetricDyson.Full.BipartiteMassNB
open Nonbacktracking
variable {V : Type*} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

def outgoing (q : G.Edge → ℝ) (y : V) : ℝ := by
  classical
  exact ∑ e, if G.tail e = y then q e else 0

def denominator (η : ℝ) (q : G.Edge → ℝ) (y : V) : ℝ := η + outgoing G q y

def vertexWeight (η : ℝ) (q : G.Edge → ℝ) (y : V) : ℝ := (denominator G η q y)⁻¹

theorem denominator_pos (η : ℝ) (q : G.Edge → ℝ)
    (hη : 0 < η) (hq : ∀ e, 0 ≤ q e) (y : V) : 0 < denominator G η q y := by
  classical
  have h : 0 ≤ outgoing G q y := Finset.sum_nonneg fun e _ => by
    split
    · exact hq e
    · exact le_rfl
  exact add_pos_of_pos_of_nonneg hη h

theorem vertexWeight_pos (η : ℝ) (q : G.Edge → ℝ)
    (hη : 0 < η) (hq : ∀ e, 0 ≤ q e) (y : V) : 0 < vertexWeight G η q y :=
  inv_pos.mpr (denominator_pos G η q hη hq y)

theorem vertexWeight_le_cavity (η : ℝ) (q : G.Edge → ℝ)
    (hη : 0 < η) (hq : ∀ e, 0 ≤ q e)
    (heq : ∀ e, denominator G η q (G.head e) * q e = 1 + q e * q (G.reverse e))
    (e : G.Edge) : vertexWeight G η q (G.head e) ≤ q e := by
  unfold vertexWeight
  rw [← one_div]
  apply (div_le_iff₀ (denominator_pos G η q hη hq _)).mpr
  have hh := heq e
  nlinarith [mul_nonneg (hq e) (hq (G.reverse e))]

theorem weighted_reverse (η : ℝ) (q : G.Edge → ℝ)
    (hη : 0 < η) (hq : ∀ e, 0 ≤ q e)
    (heq : ∀ e, denominator G η q (G.head e) * q e = 1 + q e * q (G.reverse e))
    (e : G.Edge) :
    vertexWeight G η q (G.tail e) * q e =
      vertexWeight G η q (G.head e) * q (G.reverse e) := by
  have hh := heq e
  have hr := heq (G.reverse e)
  simp only [BaseGraph.reverse_head, BaseGraph.reverse_reverse] at hr
  dsimp [vertexWeight]
  have ht := ne_of_gt (denominator_pos G η q hη hq (G.tail e))
  have hh' := ne_of_gt (denominator_pos G η q hη hq (G.head e))
  field_simp
  nlinarith

/-- The exact signed base-vertex identity. -/
theorem signed_vertex_identity (η : ℝ) (q : G.Edge → ℝ) (T : V → ℝ)
    (hη : 0 < η) (hq : ∀ e, 0 ≤ q e)
    (hT : ∀ e : G.Edge, T (G.head e) = - T (G.tail e))
    (heq : ∀ e, denominator G η q (G.head e) * q e = 1 + q e * q (G.reverse e)) :
    η * ∑ y, T y * vertexWeight G η q y = ∑ y, T y := by
  classical
  have hcancel : (∑ e, T (G.tail e) * vertexWeight G η q (G.tail e) * q e) = 0 := by
    let F : G.Edge → ℝ := fun e => T (G.tail e) * vertexWeight G η q (G.tail e) * q e
    have hrev : ∀ e, F (G.reverse e) = - F e := by
      intro e
      dsimp [F]
      rw [hT e]
      have hh := weighted_reverse G η q hη hq heq e
      linear_combination T (G.tail e) * hh
    have hh := Fintype.sum_bijective G.reverse
      (Function.Involutive.bijective G.reverse_reverse) F (fun e => F (G.reverse e)) (fun e => rfl)
    simp_rw [hrev, Finset.sum_neg_distrib] at hh
    change ∑ e, F e = 0
    linarith
  have hsum : (∑ y, T y * vertexWeight G η q y * outgoing G q y) = 0 := by
    unfold outgoing
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    convert hcancel using 1
    apply Finset.sum_congr rfl
    intro e _
    simp [mul_ite, ite_mul]
  have hpoint (y : V) : T y = η * (T y * vertexWeight G η q y) +
      T y * vertexWeight G η q y * outgoing G q y := by
    have hp := ne_of_gt (denominator_pos G η q hη hq y)
    have hh : vertexWeight G η q y * denominator G η q y = 1 := inv_mul_cancel₀ hp
    dsimp [denominator] at hh
    linear_combination -T y * hh
  calc
    _ = ∑ y, η * (T y * vertexWeight G η q y) := Finset.mul_sum ..
    _ = (∑ y, T y) - ∑ y, T y * vertexWeight G η q y * outgoing G q y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      linarith [hpoint y]
    _ = _ := by rw [hsum, sub_zero]

/-- Actual imaginary-axis Dyson values satisfy the real cavity identity. -/
theorem imaginary_cavity_identity (η : ℝ) (m : G.Edge → ℂ)
    (hη : 0 < η) (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution G.matrix (fun _ => 0) ((η : ℂ)*Complex.I) m)
    (e : G.Edge) :
    denominator G η (fun e => (m e).im) (G.head e) * (m e).im =
      1 + (m e).im * (m (G.reverse e)).im := by
  classical
  have hre := Origin.imaginary_axis_real_part_zero G.matrix η m G.matrix_nonnegative hη hm heq
  have hh := congrArg Complex.re
    (BulkNBQuantitative.NB.vertexH_product G (fun _ => 0) ((η : ℂ)*Complex.I) m hm heq e)
  have hout : (BulkDyson.NB.outgoingSum G m (G.head e)).im = outgoing G (fun e => (m e).im) (G.head e) := by
    simp [BulkDyson.NB.outgoingSum, outgoing, Complex.im_sum, apply_ite]
  simp only [BulkNBQuantitative.NB.vertexH, Complex.mul_re, Complex.sub_re,
    Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, hre e, hre (G.reverse e), mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, mul_one] at hh
  rw [hout] at hh
  dsimp [denominator]
  linarith

theorem constant_cavity_identity (c η : ℝ) (m : G.Edge → ℂ)
    (hη : 0 < η) (hm : BasicEstimates.IsUpperSolution m)
    (heq : BasicEstimates.IsDysonSolution G.matrix (fun _ => c) (Foundations.vertical c η) m)
    (e : G.Edge) :
    denominator G η (fun e => (m e).im) (G.head e) * (m e).im =
      1 + (m e).im * (m (G.reverse e)).im := by
  apply imaginary_cavity_identity G η m hη hm _ e
  intro f
  simpa [Foundations.vertical, add_sub_cancel_left] using heq f

/-- If all cavity measures have zero mass at the exceptional energy, the
signed number of base vertices must vanish. -/
theorem signed_sum_zero_of_no_atoms
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (T : V → ℝ) (c : ℝ) (m : ℂ → G.Edge → ℂ) (μ : G.Edge → Measure ℝ)
    (hT : ∀ e : G.Edge, T (G.head e) = -T (G.tail e))
    (hin : ∀ y, ∃ e : G.Edge, G.head e = y)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => c) z (m z))
    (hμ : ∀ e, IsProbabilityMeasure (μ e))
    (hrep : ∀ e, Foundations.Represents (fun z => m z e) (μ e))
    (hatom : ∀ e, μ e {c} = 0) : (∑ y, T y) = 0 := by
  let q : ℝ → G.Edge → ℝ := fun η e => (m (Foundations.vertical c η) e).im
  have hq (η : ℝ) (hη : 0 < η) : ∀ e, 0 ≤ q η e := by
    intro e
    exact (hupper _ (by simpa using hη) e).le
  have hrel (η : ℝ) (hη : 0 < η) : ∀ e,
      denominator G η (q η) (G.head e) * q η e = 1 + q η e * q η (G.reverse e) := by
    intro e
    exact constant_cavity_identity G c η _ hη
      (hupper _ (by simpa using hη)) (heq _ (by simpa using hη)) e
  have hlim (e : G.Edge) : Tendsto (fun η : ℝ => η * q η e)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [q,hatom e] using inversion.atom_formula (μ e) (fun z => m z e) c (hμ e) (hrep e)
  have hvlim (y : V) : Tendsto (fun η : ℝ => η * vertexWeight G η (q η) y)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    obtain ⟨e,he⟩ := hin y
    apply squeeze_zero' _ _ (hlim e)
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_nonneg (le_of_lt hη) (vertexWeight_pos G η (q η) hη (hq η hη) y).le
    · filter_upwards [self_mem_nhdsWithin] with η hη
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hη)
      rw [←he]
      exact vertexWeight_le_cavity G η (q η) hη (hq η hη) (hrel η hη) e
  have hs : Tendsto (fun η : ℝ => ∑ y, T y * (η * vertexWeight G η (q η) y))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hh := tendsto_finset_sum Finset.univ (fun y _ => (hvlim y).const_mul (T y))
    simpa using hh
  have hid : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (∑ y, T y * (η * vertexWeight G η (q η) y)) = ∑ y, T y := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hh := signed_vertex_identity G η (q η) T hη (hq η hη) hT (hrel η hη)
    rw [Finset.mul_sum] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro y _
    ring
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hid.mono fun _ h => h.symm)) hs

/-- Unequal signed base cardinality forces a genuine atom of a cavity measure. -/
theorem exists_atom_of_sum_ne_zero
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (T : V → ℝ) (c : ℝ) (m : ℂ → G.Edge → ℂ) (μ : G.Edge → Measure ℝ)
    (hT : ∀ e : G.Edge, T (G.head e) = -T (G.tail e))
    (hin : ∀ y, ∃ e : G.Edge, G.head e = y)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => c) z (m z))
    (hμ : ∀ e, IsProbabilityMeasure (μ e))
    (hrep : ∀ e, Foundations.Represents (fun z => m z e) (μ e))
    (hcount : (∑ y, T y) ≠ 0) : ∃ e, μ e {c} ≠ 0 := by
  by_contra h
  push_neg at h
  exact hcount (signed_sum_zero_of_no_atoms G inversion T c m μ hT hin hupper heq hμ hrep h)

/-- A base vertex has an incoming edge under the manuscript's minimum
three-neighbors assumption. -/
theorem has_incoming (hd : BulkGraph.NB.HasThreeNeighbors G) (y : V) :
    ∃ e : G.Edge, G.head e = y := by
  obtain ⟨x,hx,_⟩ := hd y y y
  exact ⟨⟨(x,y),G.symm hx⟩,rfl⟩

/-- Literal cardinality obstruction, counting base vertices. -/
theorem unequal_parts_force_atom
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (hd : BulkGraph.NB.HasThreeNeighbors G)
    (p : V → Prop) [DecidablePred p]
    (hp : ∀ x y, G.Adj x y → (p x ↔ ¬p y))
    (c : ℝ) (m : ℂ → G.Edge → ℂ) (μ : G.Edge → Measure ℝ)
    (hupper : ∀ z, 0 < z.im → BasicEstimates.IsUpperSolution (m z))
    (heq : ∀ z, 0 < z.im → BasicEstimates.IsDysonSolution G.matrix (fun _ => c) z (m z))
    (hμ : ∀ e, IsProbabilityMeasure (μ e))
    (hrep : ∀ e, Foundations.Represents (fun z => m z e) (μ e))
    (hcard : (Finset.univ.filter p).card ≠ (Finset.univ.filter (fun y => ¬p y)).card) :
    ∃ e, μ e {c} ≠ 0 ∧
      Tendsto (fun η : ℝ => (m (Foundations.vertical c η) e).im) (𝓝[>] (0 : ℝ)) atTop := by
  obtain ⟨e,he⟩ := exists_atom_of_sum_ne_zero G inversion (BipartiteMassSym.partitionSign p) c m μ
    (fun e => BipartiteMassSym.partitionSign_flip p (hp (G.tail e) (G.head e) e.property))
    (has_incoming G hd) hupper heq hμ hrep (BipartiteMassSym.sum_partitionSign_ne_zero p hcard)
  exact ⟨e,he,BoundaryMeasure.imaginary_tendsto_atTop_of_atom inversion (μ e)
    (fun z => m z e) c (hμ e) (hrep e) he⟩

/-- The atom and divergence are consequences for the canonical solution and
its actual representing probability measures, with no boundary premises. -/
theorem canonical_unequal_parts_force_atom (root : G.Edge)
    (external : Foundations.ExternalStieltjesTheory G.Edge)
    (inversion : BoundaryMeasure.ExternalStieltjesInversion)
    (hd : BulkGraph.NB.HasThreeNeighbors G)
    (p : V → Prop) [DecidablePred p]
    (hp : ∀ x y, G.Adj x y → (p x ↔ ¬p y)) (c : ℝ)
    (hcard : (Finset.univ.filter p).card ≠ (Finset.univ.filter (fun y => ¬p y)).card) :
    let m := GlobalWellPosedness.solution G.matrix (fun _ => c) G.matrix_nonnegative
    ∃ μ : G.Edge → Measure ℝ,
      (∀ e, IsProbabilityMeasure (μ e) ∧ Foundations.Represents (fun z => m z e) (μ e)) ∧
      ∃ e, μ e {c} ≠ 0 ∧
        Tendsto (fun η : ℝ => (m (Foundations.vertical c η) e).im)
          (𝓝[>] (0 : ℝ)) atTop := by
  letI : Nonempty G.Edge := ⟨root⟩
  dsimp only
  obtain ⟨_,_,_,μ,hμ⟩ := Foundations.main_theorem_one_max_norm external (fun _ => c) G.matrix_nonnegative
  refine ⟨μ,fun e => ⟨(hμ e).1,(hμ e).2.1⟩,?_⟩
  exact unequal_parts_force_atom G inversion hd p hp c _ μ
    (fun z hz => GlobalWellPosedness.solution_upper _ G.matrix_nonnegative hz)
    (fun z hz => GlobalWellPosedness.solution_equation _ G.matrix_nonnegative hz)
    (fun e => (hμ e).1) (fun e => (hμ e).2.1) hcard

end NonSymmetricDyson.Full.BipartiteMassNB
