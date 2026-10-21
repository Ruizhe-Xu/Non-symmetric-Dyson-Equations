import Dyson.Paper.SingularitiesNB

/-! Explicit graph meaning of the original Jensen equality modes. -/
noncomputable section
namespace NonSymmetricDyson.Paper.SingularitiesEqualityGraph
open Full.BulkGraph

/-- A nonzero signed alternating mode yields an actual bipartition of the
support graph. Thus the nonbipartite case of the original proof is excluded. -/
theorem alternating_bipartition {V : Type*} [Fintype V] (E : V → V → Prop) (p r : V → ℝ)
    (hp : ∀ i,p i^2=1) (hr : ∀ i,0<r i)
    (ha : ∀ i j,E i j → p j*r j= -(p i*r i)) :
    IsBipartition (E:=E) {i | p i=1} := by
  intro i j hij
  have he := (SingularitiesJensen.signed_positive_alternation p r hp hr i j (ha i j hij)).2
  change p i=1 ↔ ¬p j=1
  rw [he]
  rcases sq_eq_one_iff.mp (hp i) with hi|hi <;> norm_num [hi]

/-- The terminal calculation forces equality at every distance-two pair
in the base graph, exactly the graph condition used in the NB proof. -/
theorem nb_distance_two_constancy {V : Type*} (G : Nonbacktracking.BaseGraph V)
    (φ : V → ℝ) (h : G.Edge → ℝ)
    (hc : ∀ e,h e=φ (G.tail e)-φ (G.head e))
    (ha : ∀ e f,G.CanFollow e f → h f= -h e)
    (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w) : φ u=φ w := by
  by_cases hwu : w=u
  · simpa [hwu]
  · let e : G.Edge := ⟨(u,v),huv⟩
    let f : G.Edge := ⟨(v,w),hvw⟩
    have hh := ha e f ⟨rfl,hwu⟩
    rw [hc,hc] at hh
    change φ v-φ w= -(φ u-φ v) at hh
    linarith

end NonSymmetricDyson.Paper.SingularitiesEqualityGraph
