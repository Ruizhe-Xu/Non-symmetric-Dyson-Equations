import Dyson.Paper.SingularitiesJensen

/-! The original NB equality-space and terminal-equation argument,
revised source lines 2903–3071. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.SingularitiesNB
open Nonbacktracking Full.BulkGraph
variable {V : Type*} [Fintype V] (G : BaseGraph V)

/-- Minimum degree three turns rowwise Jensen equality into a function of
the initial vertex, and its row mean into the same function at the head. -/
theorem equality_space (deg : NB.HasThreeNeighbors G) (y c : G.Edge → ℝ)
    (hy : ∀ e f, G.CanFollow e f → y f=c e) :
    ∃ φ : V → ℝ, ∀ e, y e=φ (G.tail e) ∧ c e=φ (G.head e) := by
  have heq (e f : G.Edge) (ht : G.tail e=G.tail f) : y e=y f := by
    obtain ⟨v,hv,hve,hvf⟩ := deg (G.tail e) (G.head e) (G.head f)
    let d : G.Edge := ⟨(v,G.tail e),G.symm hv⟩
    exact (hy d e ⟨rfl,Ne.symm hve⟩).trans (hy d f ⟨ht,Ne.symm hvf⟩).symm
  let next (v : V) : V := (deg v v v).choose
  have hn (v : V) : G.Adj v (next v) := (deg v v v).choose_spec.1
  let out (v : V) : G.Edge := ⟨(v,next v),hn v⟩
  let φ : V → ℝ := fun v => y (out v)
  have hout (e : G.Edge) : y e=φ (G.tail e) := heq e (out (G.tail e)) rfl
  refine ⟨φ,fun e => ⟨hout e,?_⟩⟩
  obtain ⟨w,hw,hwe,_⟩ := deg (G.head e) (G.tail e) (G.tail e)
  let f : G.Edge := ⟨(G.head e,w),hw⟩
  exact (hy e f ⟨rfl,hwe⟩).symm.trans (hout f)

def outgoing (v : G.Edge → ℝ) (x : V) : ℝ :=
  ∑ f, if G.tail f=x then v f else 0

theorem outgoing_eq (v : G.Edge → ℝ) (e : G.Edge) :
    outgoing G v (G.head e) = (∑ f,G.matrix e f*v f)+v (G.reverse e) := by
  have h := Full.BulkDyson.NB.outgoingSum_eq G (fun f => (v f : ℂ)) e
  have hr := congrArg Complex.re h
  simpa [outgoing,Full.BulkDyson.NB.outgoingSum,apply_ite] using hr

/-- The NB center and reverse identities, and the exclusion of a zero
terminal denominator by the positive products m_e h_e. These are the
substantive algebraic steps of the paper's original NB contradiction. -/
theorem terminal_equations_force_alternation
    (a : V → ℝ) (τ : ℝ) (m h : G.Edge → ℝ) (φ : V → ℝ)
    (hm : ∀ e,m e≠0) (hpos : ∀ e,0 < m e*h e)
    (hφ : ∀ e,h e=φ (G.tail e)-φ (G.head e))
    (hperron : ∀ e,h e=m e*(∑ f,G.matrix e f*m f*h f))
    (hdyson : ∀ e,-(m e)⁻¹=τ-a (G.head e)+∑ f,G.matrix e f*m f) :
    ∀ e f,G.CanFollow e f → h f = -h e := by
  let M : V → ℝ := outgoing G (fun f => m f*h f)
  let H : V → ℝ := fun v => τ-a v+outgoing G m v
  have hrev (e : G.Edge) : h (G.reverse e) = -h e := by
    rw [hφ,hφ]
    simp only [BaseGraph.reverse_tail,BaseGraph.reverse_head]
    ring
  have hcenter (e : G.Edge) : (1-m e*m (G.reverse e))*h e=m e*M (G.head e) := by
    have ho := outgoing_eq G (fun f => m f*h f) e
    have hp := hperron e
    have hs : (∑ f,G.matrix e f*(m f*h f))=(∑ f,G.matrix e f*m f*h f) := by
      apply Finset.sum_congr rfl
      intro f _
      ring
    rw [hs,hrev] at ho
    dsimp [M]
    linear_combination hp - m e * ho
  have hreverse (e : G.Edge) : H (G.head e)*m e=m e*m (G.reverse e)-1 := by
    have ho := outgoing_eq G m e
    have hd := hdyson e
    have hinv : m e*(m e)⁻¹=1 := mul_inv_cancel₀ (hm e)
    dsimp [H]
    rw [ho]
    linear_combination -(m e)*hd - hinv
  have hterminal (e : G.Edge) : M (G.head e) = -H (G.head e)*h e := by
    have hh := hcenter e
    have hr := hreverse e
    have he : m e*(M (G.head e)+H (G.head e)*h e)=0 := by
      linear_combination -hh + h e*hr
    have hz := (mul_eq_zero.mp he).resolve_left (hm e)
    linarith
  have hnonzero (e : G.Edge) : H (G.head e) ≠ 0 := by
    intro hz
    have hr := hreverse e
    rw [hz,zero_mul] at hr
    have hp := mul_pos (hpos e) (hpos (G.reverse e))
    rw [hrev] at hp
    have ht : (m e*h e)*(m (G.reverse e)* -h e) =
        -(m e*m (G.reverse e))*h e^2 := by ring
    rw [ht] at hp
    have hh : m e*m (G.reverse e)=1 := by linarith
    rw [hh] at hp
    nlinarith [sq_nonneg (h e)]
  have hequal (e f : G.Edge) (hh : G.head e=G.head f) : h e=h f := by
    have he := hterminal e
    have hf := hterminal f
    rw [← hh] at hf
    exact (mul_left_cancel₀ (neg_ne_zero.mpr (hnonzero e))) (he.symm.trans hf)
  intro e f hef
  have hh := hequal e (G.reverse f) hef.1
  rw [hrev] at hh
  linarith

/-- For an alternating nonzero NB mode, the original Perron and Dyson
identities force the terminal potential to equal the boundary energy. -/
theorem alternating_forces_terminal_potential
    (a : V → ℝ) (τ : ℝ) (m h : G.Edge → ℝ)
    (hm : ∀ e,m e≠0) (hh : ∀ e,h e≠0)
    (hp : ∀ e,h e=m e*(∑ f,G.matrix e f*m f*h f))
    (hd : ∀ e,-(m e)⁻¹=τ-a (G.head e)+∑ f,G.matrix e f*m f)
    (ha : ∀ e f,G.CanFollow e f → h f= -h e) :
    ∀ e,a (G.head e)=τ := by
  intro e
  have hs : (∑ f,G.matrix e f*m f*h f)=
      -(h e)*(∑ f,G.matrix e f*m f) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hef : G.CanFollow e f
    · rw [ha e f hef];ring
    · simp [BaseGraph.matrix,hef]
  have he := hp e
  rw [hs] at he
  have hz : h e*(1+m e*(∑ f,G.matrix e f*m f))=0 := by nlinarith
  have hrow := (mul_eq_zero.mp hz).resolve_left (hh e)
  have hde := hd e
  have hinv : m e*(m e)⁻¹=1 := mul_inv_cancel₀ (hm e)
  have hz' : m e*(τ-a (G.head e))=0 := by
    linear_combination -(m e)*hde - hinv - hrow
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (hm e))).symm

end NonSymmetricDyson.Paper.SingularitiesNB
