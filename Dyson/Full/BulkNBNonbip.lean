import Dyson.Full.BulkNBQuantitative
import Dyson.Full.BulkStrip

noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Full.BulkNBNonbip
universe u
open Resonance Nonbacktracking BulkQuantitative BulkNBQuantitative

theorem normalized_product_square_error (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖((BulkPhase.normalize x hx ^ 2 * BulkPhase.normalize y hy ^ 2 : Circle) : ℂ) - 1‖ =
      2 * |(x * y).im| / ‖x * y‖ := by
  rw [← mul_pow]
  change ‖((BulkPhase.normalize x hx * BulkPhase.normalize y hy : Circle) : ℂ) ^ 2 - 1‖ = _
  rw [unit_square_im]
  have he : ((BulkPhase.normalize x hx * BulkPhase.normalize y hy : Circle) : ℂ) =
      x * y / ((‖x‖ * ‖y‖ : ℝ) : ℂ) := by
    change x / (‖x‖ : ℂ) * (y / (‖y‖ : ℂ)) = _
    rw [Complex.ofReal_mul]
    ring
  rw [he, Complex.div_ofReal_im, abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), norm_mul]
  ring

theorem inverse_phase_error (p q v : Circle) (A B : ℝ)
    (hprod : ‖((p * q : Circle) : ℂ) - 1‖ ≤ A)
    (herr : ‖(q : ℂ) - v‖ ≤ B) : ‖(p : ℂ) - ((v⁻¹ : Circle) : ℂ)‖ ≤ A + B := by
  have hnorm : ‖(p : ℂ) - ((v⁻¹ : Circle) : ℂ)‖ = ‖(p * v : Circle) - (1 : ℂ)‖ := by
    have he : ((p * v : Circle) : ℂ) - 1 = ((p : ℂ) - ((v⁻¹ : Circle) : ℂ)) * v := by
      simp only [Circle.coe_mul, Circle.coe_inv]
      have hv : (v : ℂ) ≠ 0 := by simpa using Circle.coe_ne_zero v
      field_simp
    rw [he, norm_mul, Circle.norm_coe, mul_one]
  rw [hnorm]
  have he : ((p * v : Circle) : ℂ) - 1 =
      (((p * q : Circle) : ℂ) - 1) + (p : ℂ) * ((v : ℂ) - q) := by
    simp only [Circle.coe_mul]
    ring
  rw [he]
  calc
    _ ≤ ‖((p * q : Circle) : ℂ) - 1‖ + ‖(p : ℂ) * ((v : ℂ) - q)‖ := norm_add_le _ _
    _ = ‖((p * q : Circle) : ℂ) - 1‖ + ‖(q : ℂ) - v‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]
      congr 1
      exact norm_sub_rev _ _
    _ ≤ _ := add_le_add hprod herr

variable {V : Type u} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

theorem vertex_im_lower (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hz : 0 ≤ z.im) (hm : BasicEstimates.IsUpperSolution m)
    (e : G.Edge) : (m (G.reverse e)).im ≤ (NB.vertexH G a z m (G.head e)).im := by
  have hh : (m (G.reverse e)).im ≤ (BulkDyson.NB.outgoingSum G m (G.head e)).im := by
    unfold BulkDyson.NB.outgoingSum
    rw [Complex.im_sum]
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun f : G.Edge => (if G.tail f = G.head e then m f else 0).im)
      (fun f _ => by dsimp only; split_ifs; exact (hm f).le; simp) (Finset.mem_univ (G.reverse e))
    simpa using hs
  simp only [NB.vertexH, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
  linarith

theorem small_phase_descent
    (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hconn : StronglyConnected G.CanFollow)
    (rho c b M delta : ℝ) (hr : 0 < rho) (hc : 0 < c) (hb : 0 < b) (hM : 0 < M)
    (hdel : 0 ≤ delta) (hz : 0 ≤ z.im)
    (hy : ∀ e, c * rho ≤ (m e).im) (hlo : ∀ e, b ≤ ‖m e‖) (hn : ∀ e, ‖m e‖ ≤ M)
    (v : G.Edge → Circle) (hv : CycleResonant G.CanFollow v)
    (herr : ∀ e, ‖(positivePhase m (BasicEstimates.component_ne_zero hm) e : ℂ) - v e‖ ≤ delta)
    (hsmall : delta < c * rho / M) :
    ∃ phi : V → Circle,
      (∀ y, 2 * b * c * rho / (1 + M ^ 2) ≤ ‖(phi y : ℂ) - 1‖) ∧
      PhaseDefect.delta G.Adj phi ≤ (2 * M ^ 2 + 1) * delta := by
  let H := NB.vertexH G a z m
  have hHim (y : V) : c * rho ≤ (H y).im := by
    obtain ⟨x, hxy, _, _⟩ := hd y y y
    let e : G.Edge := ⟨(x,y), G.symm hxy⟩
    exact (hy (G.reverse e)).trans (vertex_im_lower G a z m hz hm e)
  have hH0 (y : V) : H y ≠ 0 := by
    intro he
    have hh := hHim y
    rw [he, Complex.zero_im] at hh
    nlinarith [mul_pos hc hr]
  let phi (y : V) := BulkPhase.normalize (H y) (hH0 y) ^ 2
  have hunit (g : G.Edge) :
      |((BulkPhase.normalize (m g) (BasicEstimates.component_ne_zero hm g) *
        BulkPhase.normalize (m (G.reverse g)) (BasicEstimates.component_ne_zero hm (G.reverse g)) : Circle) : ℂ).im| ≤ delta :=
    unit_product_error _ _ (v g) (v (G.reverse g))
      (BulkGraph.NB.resonant_reverse_product G hd root hconn v hv g) delta (herr g) (herr (G.reverse g))
  have hnormphase (g : G.Edge) : c * rho / M ≤
      (BulkPhase.normalize (m g) (BasicEstimates.component_ne_zero hm g) : ℂ).im := by
    change c * rho / M ≤ (m g / (‖m g‖ : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_le_div₀ (hm g).le (hy g)
      (norm_pos_iff.mpr (BasicEstimates.component_ne_zero hm g)) (hn g)
  have hrevre (g : G.Edge) : (m g * m (G.reverse g)).re ≤ 0 :=
    real_product_re_nonpositive _ _ (BasicEstimates.component_ne_zero hm g)
      (BasicEstimates.component_ne_zero hm (G.reverse g)) (c * rho / M) delta
      (hnormphase g) (hnormphase (G.reverse g)) hsmall (hunit g)
  have hrevi (g : G.Edge) : |(H (G.head g) * m g).im| ≤ M ^ 2 * delta := by
    rw [show H (G.head g) * m g = m g * m (G.reverse g) - 1 from NB.vertexH_product G a z m hm hsol g]
    have hh := real_product_error _ _ (BasicEstimates.component_ne_zero hm g)
      (BasicEstimates.component_ne_zero hm (G.reverse g)) (v g) (v (G.reverse g))
      (BulkGraph.NB.resonant_reverse_product G hd root hconn v hv g) delta (herr g) (herr (G.reverse g))
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul (hn g) (hn (G.reverse g)) (norm_nonneg _) hM.le).trans_eq (by ring)) hdel)
  have hprodL (g : G.Edge) : 1 ≤ ‖H (G.head g) * m g‖ := by
    rw [show H (G.head g) * m g = m g * m (G.reverse g) - 1 from NB.vertexH_product G a z m hm hsol g]
    have hh := (neg_le_abs ((m g * m (G.reverse g) - 1).re)).trans
      (Complex.abs_re_le_norm (m g * m (G.reverse g) - 1))
    simp only [Complex.sub_re, Complex.one_re] at hh
    linarith [hrevre g]
  have hHnorm (y : V) : ‖H y‖ ≤ (1 + M ^ 2) / b := by
    obtain ⟨x, hxy, _, _⟩ := hd y y y
    let e : G.Edge := ⟨(x,y), G.symm hxy⟩
    have hh : ‖H y‖ * ‖m e‖ ≤ 1 + M ^ 2 := by
      rw [← norm_mul, show H y * m e = m e * m (G.reverse e) - 1 from NB.vertexH_product G a z m hm hsol e]
      calc
        _ ≤ ‖m e * m (G.reverse e)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ M * M + 1 := by
          rw [norm_mul, norm_one]
          exact add_le_add_right (mul_le_mul (hn e) (hn (G.reverse e)) (norm_nonneg _) hM.le) 1
        _ = _ := by ring
    apply (le_div_iff₀ hb).mpr
    exact (mul_le_mul_of_nonneg_left (hlo e) (norm_nonneg _)).trans hh
  refine ⟨phi, ?_, ?_⟩
  · intro y
    change _ ≤ ‖(BulkPhase.normalize (H y) (hH0 y) : ℂ) ^ 2 - 1‖
    rw [unit_square_im]
    have him : (BulkPhase.normalize (H y) (hH0 y) : ℂ).im = (H y).im / ‖H y‖ := by
      change (H y / (‖H y‖ : ℂ)).im = _
      rw [Complex.div_ofReal_im]
    rw [him, abs_of_pos (div_pos ((mul_pos hc hr).trans_le (hHim y)) (norm_pos_iff.mpr (hH0 y)))]
    have hh := div_le_div₀ ((mul_pos hc hr).trans_le (hHim y)).le (hHim y)
      (norm_pos_iff.mpr (hH0 y)) (hHnorm y)
    calc
      _ = 2 * (c * rho / ((1 + M ^ 2) / b)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  · obtain ⟨omega, homega⟩ := (BulkGraph.NB.resonance_iff_vertex_potentials G hd root hconn v).mp hv
    apply (BulkPhase.delta_le_edgeDefect G.Adj phi omega).trans
    letI : Fintype G.Edge := Subtype.fintype (fun p : V × V => G.Adj p.1 p.2)
    unfold PhaseDefect.edgeDefect
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro edge
    let g : G.Edge := ⟨(edge.val.2, edge.val.1), G.symm edge.property⟩
    have hprod : ‖((phi (G.head g) * positivePhase m (BasicEstimates.component_ne_zero hm) g : Circle) : ℂ) - 1‖ ≤
        2 * M ^ 2 * delta := by
      rw [show phi (G.head g) = BulkPhase.normalize (H (G.head g)) (hH0 _) ^ 2 from rfl]
      change ‖((BulkPhase.normalize (H (G.head g)) (hH0 _) ^ 2 *
        BulkPhase.normalize (m g) (BasicEstimates.component_ne_zero hm g) ^ 2 : Circle) : ℂ) - 1‖ ≤ _
      rw [normalized_product_square_error]
      have hh := (div_le_self (by positivity : 0 ≤ 2 * |(H (G.head g) * m g).im|) (hprodL g)).trans
        (mul_le_mul_of_nonneg_left (hrevi g) (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith
    have hh := inverse_phase_error (phi (G.head g)) (positivePhase m (BasicEstimates.component_ne_zero hm) g)
      (v g) (2 * M ^ 2 * delta) delta hprod (herr g)
    have hi : (v g)⁻¹ = (omega edge.val.1)⁻¹ * omega edge.val.2 := by
      rw [homega]
      simp [g, BaseGraph.head, BaseGraph.tail]
    rw [hi] at hh
    change ‖(phi edge.val.1 : ℂ) - (((omega edge.val.1)⁻¹ * omega edge.val.2 : Circle) : ℂ)‖ ≤ _
    simpa [g, BaseGraph.head, mul_add, add_mul, mul_assoc] using hh


/-- Approximate physical NB resonance on a non-bipartite base graph stays a
uniform multiple of rho away from the resonance set. -/
theorem rho_le_distance (external : BulkTorus.FiniteTorusErrorBound.{u})
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)
    (b M c : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m),
      BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m →
      0 ≤ z.im → 0 < rho → (∀ e, c * rho ≤ (m e).im) →
      (∀ e, b ≤ ‖m e‖) → (∀ e, ‖m e‖ ≤ M) →
      rho ≤ C * BulkTorus.resonanceDistance G.CanFollow
        (positivePhase m (BasicEstimates.component_ne_zero hm)) := by
  obtain ⟨T, hT, htorus⟩ := BulkTorus.distance_le_defect G.Adj external
  let C1 := (1 + M ^ 2) * T * (2 * M ^ 2 + 1) / (2 * b * c)
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  refine ⟨C1 + M / c, by positivity, ?_⟩
  intro a z m rho hm hsol hz hr hy hlo hn
  let phase := positivePhase m (BasicEstimates.component_ne_zero hm)
  let delta := BulkTorus.resonanceDistance G.CanFollow phase
  have hd0 : 0 ≤ delta := BulkTorus.resonanceDistance_nonnegative G.CanFollow phase
  obtain ⟨v, hv, he⟩ := BulkDistance.exists_nearest G.CanFollow phase
  have herr (e : G.Edge) : ‖(phase e : ℂ) - (v e : ℂ)‖ ≤ delta := by
    have hh := norm_le_pi_norm (BulkTorus.difference phase v) e
    simpa only [he] using hh
  by_cases hs : delta < c * rho / M
  · obtain ⟨phi, hphi, hdefect⟩ := small_phase_descent G a z m hm hsol hd root
      (BulkConnectivity.NB.stronglyConnected G hd hbase) rho c b M delta
      hr hc hb hM hd0 hz hy hlo hn v hv herr hs
    have hh := (hphi (G.tail root)).trans (norm_le_pi_norm (BulkTorus.difference phi 1) (G.tail root))
    rw [← BulkDistance.nonbipartite_distance G.Adj (fun _ _ h => G.symm h) hbase hnb phi] at hh
    have ht := (htorus phi).trans (mul_le_mul_of_nonneg_left hdefect hT.le)
    have hmain := hh.trans ht
    have hr' : rho ≤ C1 * delta := by
      have hm' := (div_le_iff₀ (by positivity : 0 < 1 + M ^ 2)).mp hmain
      dsimp [C1]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : 0 < 2 * b * c)).mpr
      nlinarith
    have hn : 0 ≤ M / c * delta := by positivity
    change rho ≤ (C1 + M / c) * delta
    nlinarith
  · have hh := (div_le_iff₀ hM).mp (le_of_not_gt hs)
    have hr' : rho ≤ M / c * delta := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      nlinarith
    have hn : 0 ≤ C1 * delta := by positivity
    change rho ≤ (C1 + M / c) * delta
    nlinarith

/-- The original stronger non-bipartite NB strip estimate C/rho². -/
theorem nonbipartite_strip_bound (external : BulkTorus.FiniteTorusErrorBound.{u})
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hbase : StronglyConnected G.Adj)
    (hnb : ¬ ∃ part : Set V, BulkGraph.IsBipartition (E := G.Adj) part)
    (b M c P : ℝ) (hb : 0 < b) (hM : 0 < M) (hc : 0 < c) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : V → ℝ) (z : ℂ) (m : G.Edge → ℂ) (rho : ℝ),
      ∀ (hm : BasicEstimates.IsUpperSolution m),
      BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) z m →
      0 ≤ z.im → 0 < rho → rho ≤ P →
      (∀ e, c * rho ≤ (m e).im) → (∀ e, (m e).im ≤ rho) →
      (∀ e, b ≤ ‖m e‖) → (∀ e, ‖m e‖ ≤ M) → ∀ x : G.Edge → ℂ,
      rho ^ 2 * ‖x‖ ≤ C * ‖InteriorStability.stabilityOperator G.matrix m x‖ := by
  letI : Nonempty G.Edge := ⟨root⟩
  have heq : (fun e f => G.matrix e f ≠ 0) = G.CanFollow := by
    funext e f
    apply propext
    by_cases h : G.CanFollow e f <;> simp [BaseGraph.matrix, h]
  have hcS : StronglyConnected (fun e f => G.matrix e f ≠ 0) := by
    rw [heq]
    exact BulkConnectivity.NB.stronglyConnected G hd hbase
  have hsupport (e f : G.Edge) (h : G.matrix e f ≠ 0) : (1 : ℝ) ≤ G.matrix e f := by
    unfold BaseGraph.matrix at h ⊢
    split_ifs with hh
    · norm_num
    · exact False.elim (h (by simp [hh]))
  obtain ⟨C0, hC0, hbound⟩ := BulkPhysical.distance_and_height_bound external G.matrix
    G.matrix_nonnegative hcS b M c 1 P hb hM hc (by norm_num) hP hsupport
  obtain ⟨C1, hC1, hdist⟩ := rho_le_distance G external hd root hbase hnb b M c hb hM hc
  refine ⟨C1 ^ 2 * C0, by positivity, ?_⟩
  intro a z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  have hd := hdist a z m rho hm hsol hz hr hylo hlo hhi
  let delta := BulkTorus.resonanceDistance G.CanFollow (positivePhase m (BasicEstimates.component_ne_zero hm))
  have hd0 : 0 ≤ delta := BulkTorus.resonanceDistance_nonnegative _ _
  have hsquare : rho ^ 2 ≤ C1 ^ 2 * delta ^ 2 := by
    have hs := (sq_le_sq₀ hr.le (mul_nonneg hC1.le hd0)).mpr hd
    nlinarith
  have hphys := hbound (G.terminalShift a) z m rho hm hsol hz hr hrP hylo hyhi hlo hhi x
  rw [← BulkStrip.positive_distance, heq] at hphys
  change (delta ^ 2 + z.im) * ‖x‖ ≤ _ at hphys
  have h1 := mul_le_mul_of_nonneg_right hsquare (norm_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hphys (sq_nonneg C1)
  have hn : 0 ≤ C1 ^ 2 * z.im * ‖x‖ := by positivity
  nlinarith

end NonSymmetricDyson.Full.BulkNBNonbip
