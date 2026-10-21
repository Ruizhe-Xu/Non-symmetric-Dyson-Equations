import Dyson.Paper.SingularitiesNondegenerate

/-! Honest finite reindexing of the original NB nondegeneracy argument. -/
noncomputable section
open scoped BigOperators Classical
namespace NonSymmetricDyson.Paper.SingularitiesReindex
open Nonbacktracking Full.Singularities Full.BulkGraph
variable {n : ℕ} {V : Type*} [Fintype V] (G : BaseGraph V)

/-- The original NB argument applies to a matrix indexed by Fin n only when
an actual edge-index equivalence and actual terminal-potential identities are
provided. -/
theorem nb_positive_reindex (deg : NB.HasThreeNeighbors G) (e : Fin n ≃ G.Edge)
    (S : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (av : V → ℝ)
    (hS : ∀ i j,S i j=G.matrix (e i) (e j))
    (ha : ∀ i,a i=av (G.head (e i)))
    (τ : ℝ) (m p q r l u : Fin n → ℝ)
    (hp : ∀ i,p i^2=1) (hq : ∀ i,0 < q i)
    (hr : ∀ i,0 < r i) (hl : ∀ i,0 < l i)
    (hm : ∀ i,m i=p i*q i)
    (hFr : ∀ i,∑ j,(q i*S i j*q j)*r j=r i)
    (hlF : ∀ j,∑ i,l i*(q i*S i j*q j)=l j)
    (hu : ∀ i,u i-∑ j,(q i*S i j*q j)*u j=p i*r i^2)
    (hsol : ∀ i,-(m i)⁻¹=τ-a i+∑ j,S i j*m j)
    (hnot : ¬∀ i,a i=τ) :
    0 < cubicCoefficient (fun i j => q i*S i j*q j) p l r u := by
  have hsum (f : Fin n → ℝ) : (∑ g:G.Edge,f (e.symm g))=∑ i,f i := e.symm.sum_comp f
  have hfr (g:G.Edge) : ∑ f,(q (e.symm g)*G.matrix g f*q (e.symm f))*r (e.symm f)=r (e.symm g) := by
    have hh := hFr (e.symm g)
    rw [← hsum] at hh
    simpa only [hS,e.apply_symm_apply] using hh
  have hlf (g:G.Edge) : ∑ f,l (e.symm f)*(q (e.symm f)*G.matrix f g*q (e.symm g))=l (e.symm g) := by
    have hh := hlF (e.symm g)
    rw [← hsum] at hh
    simpa only [hS,e.apply_symm_apply] using hh
  have hu' (g:G.Edge) : u (e.symm g)-∑ f,(q (e.symm g)*G.matrix g f*q (e.symm f))*u (e.symm f)=
      p (e.symm g)*r (e.symm g)^2 := by
    have hh := hu (e.symm g)
    rw [← hsum] at hh
    simpa only [hS,e.apply_symm_apply] using hh
  have hsol' (g:G.Edge) : -(m (e.symm g))⁻¹=τ-av (G.head g)+∑ f,G.matrix g f*m (e.symm f) := by
    have hh := hsol (e.symm g)
    rw [← hsum] at hh
    simpa only [hS,ha,e.apply_symm_apply] using hh
  have hnot' : ¬∀ g:G.Edge,av (G.head g)=τ := by
    intro hh
    apply hnot
    intro i
    rw [ha]
    exact hh (e i)
  have hh := SingularitiesNondegenerate.nb_positive G deg av τ
    (m ∘ e.symm) (p ∘ e.symm) (q ∘ e.symm) (r ∘ e.symm) (l ∘ e.symm) (u ∘ e.symm)
    (fun g => hp _) (fun g => hq _) (fun g => hr _) (fun g => hl _)
    (fun g => hm _) hfr hlf hu' hsol' hnot'
  have heq : cubicCoefficient (fun g f => q (e.symm g)*G.matrix g f*q (e.symm f))
      (p ∘ e.symm) (l ∘ e.symm) (r ∘ e.symm) (u ∘ e.symm) =
      cubicCoefficient (fun i j => q i*S i j*q j) p l r u := by
    unfold cubicCoefficient
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro g _
    rw [← hsum (fun j => (q (e.symm g)*S (e.symm g) j*q j)*u j)]
    simp only [Function.comp_apply,hS,e.apply_symm_apply]
  rw [← heq]
  exact hh
end NonSymmetricDyson.Paper.SingularitiesReindex
