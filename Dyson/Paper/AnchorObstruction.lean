import Dyson.Full.CyclicGlobalAnalytic
import Dyson.Full.NBSupportRadius

/-! Why the prescribed anchor height must be among the fixed parameters in M7.
Two exact quadratic Dyson branches coalesce at an edge.  Closeness with a
height-independent constant cannot select the physical branch. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter Set

namespace NonSymmetricDyson.Paper.AnchorObstruction
open Full CyclicExample

def physical (r : ℝ) (z : ℂ) : ℂ := scalar (z / (r : ℂ)) / (r : ℂ)
def other (r : ℝ) (z : ℂ) : ℂ := -z / (r : ℂ)^2 - physical r z
def edgePoint (r t : ℝ) : ℂ := (2*r : ℝ) + t*Complex.I

theorem physical_quadratic (r : ℝ) (hr : 0 < r) (z : ℂ) :
    (r : ℂ)^2 * physical r z ^ 2 + z * physical r z + 1 = 0 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := scalar_quadratic (z/(r:ℂ))
  unfold physical
  field_simp [hr0] at h ⊢
  linear_combination h

theorem other_quadratic (r : ℝ) (hr : 0 < r) (z : ℂ) :
    (r : ℂ)^2 * other r z ^ 2 + z * other r z + 1 = 0 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := physical_quadratic r hr z
  unfold other
  field_simp [hr0]
  linear_combination (r:ℂ)^2 * h

theorem physical_upper (r : ℝ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    0 < (physical r z).im := by
  have hzi : 0 < (z/(r:ℂ)).im := by simpa using div_pos hz hr
  have h := CyclicGeneral.scalar_upper hzi
  simpa [physical] using div_pos h hr

theorem other_lower (r : ℝ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    (other r z).im < 0 := by
  have hp := physical_upper r hr hz
  have hd : 0 < z.im / r^2 := div_pos hz (sq_pos_of_pos hr)
  simp only [other, Complex.sub_im, Complex.neg_im]
  rw [← Complex.ofReal_pow]
  simp only [Complex.div_ofReal_im, Complex.neg_im, neg_div]
  linarith

theorem branches_ne (r : ℝ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    other r z ≠ physical r z := by
  intro h
  have hl := other_lower r hr hz
  rw [h] at hl
  linarith [physical_upper r hr hz]

theorem scalar_continuous_at_edge : ContinuousAt scalar (2 : ℂ) := by
  have hp : ContinuousAt (fun w : ℂ => w ^ ((2 : ℂ)⁻¹)) 0 := by
    apply Complex.continuousAt_cpow_const_of_re_pos (by simp)
    norm_num
  have hq : ContinuousAt root (2 : ℂ) := by
    simpa [root] using hp.comp_of_eq
      (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)
  exact (continuousAt_id.neg.add (hq.const_mul Complex.I)).div_const 2

theorem scalar_edge : scalar (2 : ℂ) = -1 := by
  norm_num [scalar, root]

theorem physical_continuous_at_edge (r : ℝ) (hr : 0 < r) :
    ContinuousAt (physical r) ((2*r : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply (scalar_continuous_at_edge.comp_of_eq
    (continuousAt_id.div_const (r:ℂ)) ?_).div_const (r:ℂ)
  push_cast
  field_simp
  rfl

theorem branches_agree_at_edge (r : ℝ) (hr : 0 < r) :
    other r ((2*r : ℝ) : ℂ) = physical r ((2*r : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : (((2*r:ℝ):ℂ)/(r:ℂ))=2 := by push_cast; field_simp
  simp only [other, physical, he, scalar_edge]
  push_cast
  field_simp
  <;> ring

theorem branches_arbitrarily_close (r : ℝ) (hr : 0 < r) (c : ℝ) (hc : 0 < c) :
    ∃ H : ℝ, 0 < H ∧ ∀ t ∈ Icc (0 : ℝ) H,
      ‖other r (edgePoint r t) - physical r (edgePoint r t)‖ < c := by
  have hp := physical_continuous_at_edge r hr
  have ho : ContinuousAt (other r) ((2*r:ℝ):ℂ) :=
    (continuousAt_id.neg.div_const ((r:ℂ)^2)).sub hp
  have hv : ContinuousAt (edgePoint r) (0 : ℝ) := by unfold edgePoint; fun_prop
  have hnorm : ContinuousAt (fun t : ℝ =>
      ‖other r (edgePoint r t)-physical r (edgePoint r t)‖) 0 := by
    apply ((ho.sub hp).norm).comp_of_eq hv
    simp [edgePoint]
  have hev : ∀ᶠ t in 𝓝 (0:ℝ),
      ‖other r (edgePoint r t)-physical r (edgePoint r t)‖ < c := by
    apply hnorm.eventually (gt_mem_nhds ?_)
    dsimp only
    have he : edgePoint r 0 = ((2*r:ℝ):ℂ) := by simp [edgePoint]
    rw [he, branches_agree_at_edge r hr, sub_self, norm_zero]
    exact hc
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ/2, by positivity, ?_⟩
  intro t ht
  apply hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

variable {ι : Type*} [Fintype ι]

theorem quadratic_is_dyson (S : Matrix ι ι ℝ) (r : ℝ)
    (hrow : ∀ i, ∑ j, S i j = r^2) (z w : ℂ)
    (he : (r:ℂ)^2*w^2+z*w+1=0) :
    BasicEstimates.IsDysonSolution S (fun _ => 0) z (fun _ => w) := by
  have hw : w ≠ 0 := by intro hz; simp [hz] at he
  intro i
  have ha : Model.action S (fun _ => w) i=(r:ℂ)^2*w := by
    rw [Model.action_apply, ← Finset.sum_mul]
    have hc : (∑ j, (S i j:ℂ))=(r:ℂ)^2 := by exact_mod_cast hrow i
    rw [hc]
  change -w⁻¹=z-(0:ℂ)+Model.action S (fun _ => w) i
  rw [ha, sub_zero]
  apply mul_left_cancel₀ hw
  simp only [mul_neg, mul_inv_cancel₀ hw]
  linear_combination -he

theorem canonical_is_physical (S : Matrix ι ι ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (r : ℝ) (hr : 0 < r) (hrow : ∀ i, ∑ j, S i j = r^2)
    {z : ℂ} (hz : 0 < z.im) :
    GlobalWellPosedness.solution S (fun _ => 0) hS z=fun _ => physical r z := by
  exact GlobalWellPosedness.solution_eq_of_upper_solution (fun _ => 0) hS hz
    (fun _ => physical_upper r hr hz)
    (quadratic_is_dyson S r hrow z _ (physical_quadratic r hr z))

theorem competing_branch_exact_residual (S : Matrix ι ι ℝ)
    (r : ℝ) (hr : 0 < r) (hrow : ∀ i, ∑ j, S i j = r^2) (z : ℂ) :
    Model.residual S (fun _ => 0) z (fun _ => other r z)=0 := by
  apply (Model.residual_zero_iff S (fun _ => 0) z _).mpr
  exact quadratic_is_dyson S r hrow z _ (other_quadratic r hr z)

theorem other_continuous_upper (r : ℝ) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt (other r) z := by
  have hzi : 0 < (z/(r:ℂ)).im := by simpa using div_pos hz hr
  have hs := (CyclicGeneral.scalar_analytic_upper (z/(r:ℂ)) hzi).continuousAt
  have hc : ContinuousAt (fun w : ℂ => w/(r:ℂ)) z := continuousAt_id.div_const _
  have hp : ContinuousAt (physical r) z :=
    (hs.comp_of_eq hc rfl).div_const (r:ℂ)
  exact (continuousAt_id.neg.div_const ((r:ℂ)^2)).sub hp

/-- At arbitrarily low anchors the second exact solution satisfies all path
closeness and zero-residual assumptions but is not the physical solution.
Consequently M7's closeness threshold must be allowed to depend on the fixed
positive anchor, or the statement must prescribe a quantitative anchor. -/
theorem height_uniform_selection_fails [Nonempty ι]
    (S : Matrix ι ι ℝ) (hS : ∀ i j, 0 ≤ S i j)
    (r : ℝ) (hr : 0 < r) (hrow : ∀ i, ∑ j, S i j = r^2)
    (c : ℝ) (hc : 0 < c) :
    ∃ H : ℝ, 0 < H ∧ ∀ η : ℝ, 0 < η → η ≤ H →
      ∃ g : ℝ → ι → ℂ,
        ContinuousOn g (Icc η H) ∧
        (∀ t ∈ Icc η H, ∀ i, g t i ≠ 0) ∧
        (∀ t ∈ Icc η H,
          ‖g t - GlobalWellPosedness.solution S (fun _ => 0) hS (edgePoint r t)‖ < c) ∧
        (∀ t ∈ Icc η H, Model.residual S (fun _ => 0) (edgePoint r t) (g t)=0) ∧
        g η ≠ GlobalWellPosedness.solution S (fun _ => 0) hS (edgePoint r η) := by
  obtain ⟨H,hH,hclose⟩ := branches_arbitrarily_close r hr c hc
  refine ⟨H,hH,?_⟩
  intro η hη hηH
  let g : ℝ → ι → ℂ := fun t _ => other r (edgePoint r t)
  have hz : ∀ t ∈ Icc η H, 0 < (edgePoint r t).im := by
    intro t ht
    simpa [edgePoint] using hη.trans_le ht.1
  have hgcont : ContinuousOn g (Icc η H) := by
    apply continuousOn_pi.mpr
    intro i t ht
    apply ContinuousAt.continuousWithinAt
    exact (other_continuous_upper r hr (hz t ht)).comp (by unfold edgePoint; fun_prop)
  refine ⟨g,hgcont,?_,?_,?_,?_⟩
  · intro t ht i he
    have hneg := other_lower r hr (hz t ht)
    change other r (edgePoint r t)=0 at he
    rw [he] at hneg
    exact (lt_irrefl 0 hneg)
  · intro t ht
    rw [canonical_is_physical S hS r hr hrow (hz t ht)]
    change ‖fun _ : ι => other r (edgePoint r t)-physical r (edgePoint r t)‖ < c
    simpa using hclose t ⟨(hη.trans_le ht.1).le,ht.2⟩
  · intro t ht
    exact competing_branch_exact_residual S r hr hrow (edgePoint r t)
  · rw [canonical_is_physical S hS r hr hrow (hz η ⟨le_rfl,hηH⟩)]
    intro he
    have hi := congrFun he (Classical.arbitrary ι)
    exact branches_ne r hr (hz η ⟨le_rfl,hηH⟩) hi

/-- A concrete base graph satisfying the manuscript's minimum-degree condition. -/
def tetrahedron : Nonbacktracking.BaseGraph (Fin 4) where
  Adj i j := i ≠ j
  symm := Ne.symm
  loopless _ := not_not_intro rfl

theorem tetrahedron_degree (i : Fin 4) : NBSupportRadius.degree tetrahedron i=3 := by
  rw [NBSupportRadius.degree_eq_neighbor_count]
  calc
    _ = (Finset.univ.erase i).card := by
      congr 1
      ext j
      simp [tetrahedron, ne_comm]
    _ = 3 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; norm_num

theorem tetrahedron_row_sum (e : tetrahedron.Edge) :
    (∑ f, tetrahedron.matrix e f)=2 := by
  rw [NBSupportRadius.rowSum_eq_degree_sub_one, tetrahedron_degree]
  norm_num

theorem tetrahedron_three_neighbors : BulkGraph.NB.HasThreeNeighbors tetrahedron := by
  apply BulkGraph.NB.hasThreeNeighbors_of_degree
  intro i
  have h := tetrahedron_degree i
  rw [NBSupportRadius.degree_eq_neighbor_count] at h
  exact le_of_eq h.symm

theorem tetrahedron_connected : Resonance.StronglyConnected tetrahedron.Adj := by
  intro i j
  by_cases h : i=j
  · subst j
    exact ⟨Resonance.Walk.nil i⟩
  · exact ⟨Resonance.Walk.cons h (Resonance.Walk.nil j)⟩

instance : Nonempty tetrahedron.Edge := ⟨⟨(0,1),by change (0:Fin 4) ≠ 1; decide⟩⟩

/-- The obstruction occurs for an actual unweighted NB matrix, not only for a
scalar toy model: the tetrahedron has three neighbors and row sum two. -/
theorem actual_nb_anchor_obstruction (c : ℝ) (hc : 0 < c) :
    ∃ H : ℝ, 0 < H ∧ ∀ η : ℝ, 0 < η → η ≤ H →
      ∃ g : ℝ → tetrahedron.Edge → ℂ,
        ContinuousOn g (Icc η H) ∧
        (∀ t ∈ Icc η H, ∀ i, g t i ≠ 0) ∧
        (∀ t ∈ Icc η H,
          ‖g t - GlobalWellPosedness.solution tetrahedron.matrix (fun _ => 0)
            tetrahedron.matrix_nonnegative (edgePoint (Real.sqrt 2) t)‖ < c) ∧
        (∀ t ∈ Icc η H, Model.residual tetrahedron.matrix (fun _ => 0)
          (edgePoint (Real.sqrt 2) t) (g t)=0) ∧
        g η ≠ GlobalWellPosedness.solution tetrahedron.matrix (fun _ => 0)
          tetrahedron.matrix_nonnegative (edgePoint (Real.sqrt 2) η) := by
  apply height_uniform_selection_fails tetrahedron.matrix tetrahedron.matrix_nonnegative
    (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num))
    (fun e => (tetrahedron_row_sum e).trans (Real.sq_sqrt (by norm_num)).symm) c hc

end NonSymmetricDyson.Paper.AnchorObstruction
