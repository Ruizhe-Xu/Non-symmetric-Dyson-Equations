import Dyson.Full.BulkGraph
import Dyson.Full.BulkConnectivity
import Dyson.Full.BulkPhase
import Dyson.PolynomialDyson
import Mathlib

/-! Exact restrictions on resonant physical Dyson boundary values. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.BulkDyson

open Resonance Nonbacktracking

theorem imaginary_eq_zero_of_square_norm (w : ℂ)
    (h : w^2 = (‖w‖ : ℂ)^2) : w.im = 0 := by
  have hr := congrArg Complex.re h
  have hn := Complex.normSq_eq_norm_sq w
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hr
  rw [Complex.normSq_apply] at hn
  nlinarith [sq_nonneg w.im]

theorem phase_square_ne_one (w : ℂ) (hw : 0 < w.im) :
    (BulkPhase.normalize w (by intro h; simpa [h] using hw))^2 ≠ 1 := by
  intro h
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr (by intro h; simpa [h] using hw)
  have hz : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hc := congrArg (fun u : Circle => (u : ℂ)) h
  change (w / (‖w‖ : ℂ))^2 = 1 at hc
  have hs : w^2 = (‖w‖ : ℂ)^2 := by
    field_simp at hc
    exact hc
  exact (ne_of_gt hw) (imaginary_eq_zero_of_square_norm w hs)

theorem real_product_of_squared_phase
    (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (BulkPhase.normalize x hx)^2 * (BulkPhase.normalize y hy)^2 = 1) :
    (x*y).im = 0 := by
  have hxn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hyn : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
  have hc := congrArg (fun u : Circle => (u : ℂ)) h
  change (x / (‖x‖ : ℂ))^2 * (y / (‖y‖ : ℂ))^2 = 1 at hc
  field_simp at hc
  apply imaginary_eq_zero_of_square_norm (x*y)
  rw [norm_mul, Complex.ofReal_mul]
  linear_combination hc

variable {ι : Type*} [Fintype ι]

/-- If all supported products are real, the actual polynomial equation
forces the real energy to equal every potential. -/
theorem potentials_eq_energy_of_real_products
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ) (m : ι → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a (τ : ℂ) m)
    (hreal : ∀ i j, S i j ≠ 0 → (m i * m j).im = 0) :
    ∀ i, a i = τ := by
  intro i
  have hp := PolynomialDyson.of_dyson hsol (BasicEstimates.component_ne_zero hm) i
  have hid : m i * ((τ : ℂ) - (a i : ℂ)) +
      ∑ j, (S i j : ℂ) * (m i * m j) = -1 := by
    calc
      _ = m i * ((τ : ℂ) - (a i : ℂ) + ∑ j, (S i j : ℂ) * m j) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -1 := hp.symm
  have him := congrArg Complex.im hid
  have hsum : (∑ j, (S i j : ℂ) * (m i * m j)).im = 0 := by
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hs : S i j = 0
    · simp [hs]
    · simp [Complex.mul_im, hreal i j hs]
  rw [Complex.add_im, hsum] at him
  simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_im, sub_self,
    mul_zero, Complex.sub_re, Complex.ofReal_re, zero_add, Complex.neg_im,
    Complex.one_im, neg_zero, add_zero] at him
  have hs : τ - a i = 0 := (mul_eq_zero.mp him).resolve_left (ne_of_gt (hm i))
  linarith

theorem symmetric_resonance_forces_constant_potential
    (S : Matrix ι ι ℝ) (a : ι → ℝ) (τ : ℝ) (m : ι → ℂ)
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution S a (τ : ℂ) m)
    (hres : CycleResonant (fun i j => S i j ≠ 0)
      (fun i => (BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i))^2)) :
    ∀ i, a i = τ := by
  apply potentials_eq_energy_of_real_products S a τ m hm hsol
  intro i j hij
  exact real_product_of_squared_phase (m i) (m j)
    (BasicEstimates.component_ne_zero hm i) (BasicEstimates.component_ne_zero hm j)
    (BulkGraph.symmetric_resonance_edge hsymm _ hres hij)

theorem symmetric_physical_resonance_bipartite
    (S : Matrix ι ι ℝ) (m : ι → ℂ) (root : ι)
    (hsymm : ∀ i j, S i j ≠ 0 → S j i ≠ 0)
    (hconn : StronglyConnected (fun i j => S i j ≠ 0))
    (hm : BasicEstimates.IsUpperSolution m)
    (hres : CycleResonant (fun i j => S i j ≠ 0)
      (fun i => (BulkPhase.normalize (m i) (BasicEstimates.component_ne_zero hm i))^2)) :
    ∃ part : Set ι, BulkGraph.IsBipartition (E := fun i j => S i j ≠ 0) part := by
  apply BulkGraph.bipartition_of_nontrivial_resonance hsymm hconn _ hres root
  exact phase_square_ne_one (m root) (hm root)

/-- A ratio of two nonzero real products propagates reality to a new product. -/
theorem propagate_real_products (A x y z : ℂ) (hA : A ≠ 0) (hy : y ≠ 0)
    (hx : (A*x).im = 0) (hyA : (A*y).im = 0) (hz : (y*z).im = 0) :
    (x*z).im = 0 := by
  have heq : x*z = ((A*x)/(A*y))*(y*z) := by field_simp
  rw [heq, Complex.mul_im, hz]
  simp [Complex.div_im, hx, hyA]

namespace NB

variable {V : Type*} [Fintype V] (G : BaseGraph V) [Fintype G.Edge]

def outgoingSum (m : G.Edge → ℂ) (y : V) : ℂ := by
  classical
  exact ∑ f, if G.tail f = y then m f else 0

theorem outgoingSum_eq (m : G.Edge → ℂ) (e : G.Edge) :
    outgoingSum G m (G.head e) =
      (∑ f, (G.matrix e f : ℂ) * m f) + m (G.reverse e) := by
  classical
  have ht (f : G.Edge) : (if G.tail f = G.head e then m f else 0) =
      (if G.CanFollow e f then m f else 0) + (if f = G.reverse e then m f else 0) := by
    by_cases hrev : f = G.reverse e
    · subst f
      simp [G.not_canFollow_reverse]
    · by_cases htail : G.tail f = G.head e
      · have hhead : G.head f ≠ G.tail e := by
          intro hh
          apply hrev
          apply Subtype.ext
          exact Prod.ext htail hh
        have hf : G.CanFollow e f := ⟨htail.symm, hhead⟩
        simp [hrev, htail, hf]
      · have hf : ¬ G.CanFollow e f := fun h => htail h.1.symm
        simp [hrev, htail, hf]
  unfold outgoingSum
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro f _
    by_cases hf : G.CanFollow e f <;> simp [BaseGraph.matrix, hf]
  · simp

theorem outgoingSum_im_pos (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m) (e : G.Edge) :
    0 < (outgoingSum G m (G.head e)).im := by
  classical
  unfold outgoingSum
  rw [Complex.im_sum]
  apply lt_of_lt_of_le (hm (G.reverse e))
  have hnonneg (f : G.Edge) : 0 ≤ (if G.tail f = G.head e then m f else 0).im := by
    split_ifs
    · exact (hm f).le
    · simp
  have hs := Finset.single_le_sum (fun f _ => hnonneg f) (Finset.mem_univ (G.reverse e))
  simpa using hs

def vertexDenominator (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ) (y : V) : ℂ :=
  (τ : ℂ) - (a y : ℂ) + outgoingSum G m y

theorem vertexDenominator_eq (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (τ : ℂ) m)
    (e : G.Edge) : vertexDenominator G a τ m (G.head e) =
      -(m e)⁻¹ + m (G.reverse e) := by
  rw [vertexDenominator, outgoingSum_eq, hsol e]
  simp [BaseGraph.terminalShift, add_assoc]

theorem vertexDenominator_ne_zero (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m) (e : G.Edge) :
    vertexDenominator G a τ m (G.head e) ≠ 0 := by
  have hh : 0 < (vertexDenominator G a τ m (G.head e)).im := by
    simpa [vertexDenominator] using outgoingSum_im_pos G m hm e
  intro heq
  simpa [heq] using hh

theorem real_vertex_product (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (τ : ℂ) m)
    (hreal : ∀ e, (m e * m (G.reverse e)).im = 0) (e : G.Edge) :
    (vertexDenominator G a τ m (G.head e) * m e).im = 0 := by
  rw [vertexDenominator_eq G a τ m hsol e]
  have heq : (-(m e)⁻¹ + m (G.reverse e)) * m e = -1 + m e * m (G.reverse e) := by
    field_simp [BasicEstimates.component_ne_zero hm e]
  rw [heq]
  simpa using hreal e

theorem real_turn_products (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (τ : ℂ) m)
    (hreal : ∀ e, (m e * m (G.reverse e)).im = 0)
    (e f : G.Edge) (hef : G.CanFollow e f) : (m e * m f).im = 0 := by
  apply propagate_real_products (vertexDenominator G a τ m (G.head e))
    (m e) (m (G.reverse f)) (m f)
    (vertexDenominator_ne_zero G a τ m hm e)
    (BasicEstimates.component_ne_zero hm (G.reverse f))
    (real_vertex_product G a τ m hm hsol hreal e)
  · simpa [hef.1] using real_vertex_product G a τ m hm hsol hreal (G.reverse f)
  · simpa using hreal (G.reverse f)

theorem resonance_forces_constant_terminal_potential
    (a : V → ℝ) (τ : ℝ) (m : G.Edge → ℂ)
    (hd : BulkGraph.NB.HasThreeNeighbors G) (root : G.Edge)
    (hconn : StronglyConnected G.CanFollow)
    (hm : BasicEstimates.IsUpperSolution m)
    (hsol : BasicEstimates.IsDysonSolution G.matrix (G.terminalShift a) (τ : ℂ) m)
    (hres : CycleResonant G.CanFollow
      (fun e => (BulkPhase.normalize (m e) (BasicEstimates.component_ne_zero hm e))^2)) :
    ∀ y, a y = τ := by
  classical
  have hre (e : G.Edge) : (m e * m (G.reverse e)).im = 0 :=
    real_product_of_squared_phase _ _ (BasicEstimates.component_ne_zero hm _)
      (BasicEstimates.component_ne_zero hm _)
      (BulkGraph.NB.resonant_reverse_product G hd root hconn _ hres e)
  have hpot := potentials_eq_energy_of_real_products G.matrix (G.terminalShift a) τ m hm hsol
    (fun e f hef => real_turn_products G a τ m hm hsol hre e f (by
      by_contra h
      exact hef (by simp [BaseGraph.matrix, h])))
  intro y
  obtain ⟨x, hxy, _, _⟩ := hd y y y
  let e : G.Edge := ⟨(x,y), G.symm hxy⟩
  exact hpot e

end NB
end NonSymmetricDyson.Full.BulkDyson
