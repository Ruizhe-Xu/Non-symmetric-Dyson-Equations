import Mathlib

/-! Generic finite-branch Schur elimination for actual continuous linear
operators. No Dyson equation, matrix of type weights, tree, Herglotz theorem,
or spectral measure occurs as a premise. The inverse identities follow
algebraically from the displayed operator block formulas. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.TreeSchur
universe u v w
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {J : Type v} [Fintype J]
variable {E : J → Type w} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℂ (E j)]

/-- Root Schur complement after deleting finitely many forward branches.
The supplied equivalences are the actual operators L−z and Dⱼ−z, not
abstract Green functions. No self-adjointness is needed for this algebra. -/
theorem finite_branch_resolvent_identity
    (L : H →L[ℂ] H) (D : ∀ j, E j →L[ℂ] E j)
    (root : H →L[ℂ] ℂ) (branch : ∀ j, H →L[ℂ] E j)
    (coupling : ∀ j, E j →L[ℂ] ℂ) (v : ∀ j, E j) (e : H) (a z : ℂ)
    (T : H ≃L[ℂ] H) (R : ∀ j, E j ≃L[ℂ] E j)
    (hT : ∀ x, T x = L x - z • x)
    (hR : ∀ j y, R j y = D j y - z • y)
    (hroot : ∀ x, root (L x) = a * root x + ∑ j, coupling j (branch j x))
    (hbranch : ∀ j x, branch j (L x) = D j (branch j x) + root x • v j)
    (he : root e = 1) (hebranch : ∀ j, branch j e = 0) :
    root (T.symm e) ≠ 0 ∧
      -(root (T.symm e))⁻¹ = z - a + ∑ j, coupling j ((R j).symm (v j)) := by
  let x := T.symm e
  let m := root x
  have hTx : L x-z • x = e := by rw [←hT]; exact T.apply_symm_apply e
  have hBx (j : J) : R j (branch j x) = -m • v j := by
    have hj := congrArg (branch j) hTx
    rw [map_sub,map_smul,hbranch,hebranch] at hj
    rw [hR]
    change D j (branch j x)-z • branch j x = -root x • v j
    rw [neg_smul]
    calc
      D j (branch j x)-z • branch j x =
          (D j (branch j x)+root x • v j-z • branch j x)-root x • v j := by abel
      _ = -(root x • v j) := by rw [hj]; simp
  have hpx (j : J) : branch j x = -m • (R j).symm (v j) := by
    apply (R j).injective
    rw [hBx,map_smul,(R j).apply_symm_apply]
  have hscalar : m * (a-z-∑ j, coupling j ((R j).symm (v j))) = 1 := by
    have h0 := congrArg root hTx
    rw [map_sub,map_smul,hroot,he] at h0
    simp only [hpx,map_smul,smul_eq_mul,←Finset.mul_sum] at h0
    change a*m+(-m)*(∑ j, coupling j ((R j).symm (v j)))-z*m=1 at h0
    linear_combination h0
  have hm : m ≠ 0 := by intro hm; simp [hm] at hscalar
  refine ⟨hm,?_⟩
  change -m⁻¹ = _
  have hi : a-z-∑ j, coupling j ((R j).symm (v j)) = m⁻¹ := by
    apply (mul_left_cancel₀ hm)
    rw [hscalar,mul_inv_cancel₀ hm]
  linear_combination hi

/-- Square-root edge weights enter twice, once on each side of the root
block. This is a generic weighted-forest identity, not an assumed Dyson
recursion for the type-indexed root functions. -/
theorem weighted_branch_resolvent_identity
    (L : H →L[ℂ] H) (D : ∀ j, E j →L[ℂ] E j)
    (root : H →L[ℂ] ℂ) (branch : ∀ j, H →L[ℂ] E j)
    (childRoot : ∀ j, E j →L[ℂ] ℂ) (childVector : ∀ j, E j)
    (weight : J → ℝ) (e : H) (a z : ℂ)
    (T : H ≃L[ℂ] H) (R : ∀ j, E j ≃L[ℂ] E j)
    (hT : ∀ x, T x = L x - z • x)
    (hR : ∀ j y, R j y = D j y - z • y)
    (hroot : ∀ x, root (L x) = a * root x +
      ∑ j, (weight j : ℂ) * childRoot j (branch j x))
    (hbranch : ∀ j x, branch j (L x) = D j (branch j x) +
      root x • ((weight j : ℂ) • childVector j))
    (he : root e = 1) (hebranch : ∀ j, branch j e = 0) :
    root (T.symm e) ≠ 0 ∧
      -(root (T.symm e))⁻¹ = z - a +
        ∑ j, ((weight j)^2 : ℝ) * childRoot j ((R j).symm (childVector j)) := by
  have h := finite_branch_resolvent_identity L D root branch
    (fun j => (weight j : ℂ) • childRoot j)
    (fun j => (weight j : ℂ) • childVector j) e a z T R hT hR hroot hbranch he hebranch
  refine ⟨h.1,h.2.trans ?_⟩
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul,Complex.ofReal_pow]
  ring

end NonSymmetricDyson.Paper.TreeSchur
