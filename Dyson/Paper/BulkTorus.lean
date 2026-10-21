import Dyson.Full.BulkTorus

/-! The manuscript's integer-lattice correction argument. The only imported
principles here are ordinary integer row-basis existence, the classification
of torus characters, and scalar circle geometry. No graph, Markov matrix,
Dyson solution, or resonance-distance estimate is an external premise. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.BulkTorus
universe u v w

def character {I : Type u} {J : Type v} [Fintype I] (A : Matrix J I ℤ) (x : I → Circle) : J → Circle :=
  fun j => ∏ i, x i ^ A j i

theorem character_exp {I : Type u} {J : Type v} [Fintype I]
    (A : Matrix J I ℤ) (θ : I → ℝ) (j : J) :
    character A (fun i => Circle.exp (θ i)) j = Circle.exp (∑ i, (A j i : ℝ) * θ i) := by
  have hs := map_sum Circle.expHom (fun i => (A j i : ℝ) * θ i) Finset.univ
  change Circle.exp (∑ i, (A j i : ℝ) * θ i) = ∏ i, Circle.exp ((A j i : ℝ) * θ i) at hs
  rw [hs]
  apply Finset.prod_congr rfl
  intro i _
  exact (show Circle.exp ((A j i : ℝ) * θ i) = Circle.exp (θ i) ^ A j i from by
    simpa only [zsmul_eq_mul] using map_zsmul Circle.expHom (A j i) (θ i)).symm

theorem zpow_finset_sum {K : Type*} (s : Finset K) (f : K → ℤ) (x : Circle) :
    x ^ (∑ k ∈ s, f k) = ∏ k ∈ s, x ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [hk,zpow_add,ih]

theorem character_mul {I : Type u} {J : Type v} {K : Type w} [Fintype I] [Fintype J]
    (A : Matrix J I ℤ) (C : Matrix K J ℤ) (x : I → Circle) :
    character (C * A) x = character C (character A x) := by
  funext k
  simp only [character, Matrix.mul_apply, zpow_finset_sum, ← Finset.prod_zpow, zpow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  rw [←zpow_mul,←zpow_mul,mul_comm]

/-- A genuine integral row basis of the original lattice, with integer
change-of-generator matrices in both directions and a real right inverse.
This is the standard submodule-of-Z^d basis theorem plus finite-dimensional
linear algebra. No saturation of the lattice is permitted. -/
def IntegerRowBasis : Prop :=
  ∀ {I J : Type u} [Fintype I] [Fintype J] (A : Matrix J I ℤ),
    ∃ (r : ℕ) (B : Matrix (Fin r) I ℤ) (C : Matrix (Fin r) J ℤ)
      (D : Matrix J (Fin r) ℤ) (R : Matrix I (Fin r) ℝ),
      B = C * A ∧ A = D * B ∧
      ∀ b : Fin r → ℝ, ∀ k,
        (∑ i, (B k i : ℝ) * (∑ l, R i l * b l)) = b k

/-- Scalar trigonometric facts. The first is the principal-angle bound
`dist(t,2πZ) ≤ C |exp(it)-1|`; the second is the unit-circle Lipschitz bound. -/
def CircleMetricFacts : Prop :=
  ∃ K : ℝ, 0 < K ∧
    (∀ x : Circle, |Complex.arg (x : ℂ)| ≤ K * ‖(x : ℂ) - 1‖) ∧
    (∀ s t : ℝ, ‖(Circle.exp s : ℂ) - (Circle.exp t : ℂ)‖ ≤ |s-t|)

/-- Ordinary character theory of a finite torus. -/
def ContinuousCharacterClassification : Prop :=
  ∀ {I J : Type u} [Fintype I] [Fintype J]
    (F : (I → Circle) →* (J → Circle)), Continuous F →
      ∃ A : Matrix J I ℤ, ∀ x, F x = character A x

/-- The correction θ↦θ−R b lands in the full original integer kernel. -/
theorem integer_lattice_correction {I J : Type u} [Fintype I] [Fintype J]
    (basis : IntegerRowBasis.{u}) (geometry : CircleMetricFacts)
    (A : Matrix J I ℤ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : I → Circle,
      ∃ y : I → Circle, character A y = 1 ∧
        ‖Full.BulkTorus.difference x y‖ ≤ L * ‖Full.BulkTorus.difference (character A x) 1‖ := by
  classical
  obtain ⟨r,B,C,D,R,hB,hA,hR⟩ := basis A
  obtain ⟨K,hK,harg,hexp⟩ := geometry
  let Rnorm : ℝ := ∑ i, ∑ k, |R i k|
  let Cnorm : ℝ := ∑ k, ∑ j, |(C k j : ℝ)|
  let L : ℝ := 1 + Rnorm * Cnorm * K
  have hRn : 0 ≤ Rnorm := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCn : 0 ≤ Cnorm := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro x
  let θ : I → ℝ := fun i => Complex.arg (x i : ℂ)
  let α : J → ℝ := fun j => Complex.arg (character A x j : ℂ)
  let b : Fin r → ℝ := fun k => ∑ j, (C k j : ℝ) * α j
  let correction : I → ℝ := fun i => ∑ k, R i k * b k
  let y : I → Circle := fun i => Circle.exp (θ i - correction i)
  have hx : (fun i => Circle.exp (θ i)) = x := by funext i; exact Circle.exp_arg (x i)
  have hα : (fun j => Circle.exp (α j)) = character A x := by
    funext j; exact Circle.exp_arg (character A x j)
  have hbphase (k : Fin r) : Circle.exp (b k) = character B x k := by
    change Circle.exp (∑ j, (C k j : ℝ) * α j) = _
    rw [←character_exp C α k,hα,hB,character_mul]
  have hyB : character B y = 1 := by
    funext k
    rw [character_exp]
    have hs : (∑ i, (B k i : ℝ) * (θ i-correction i)) =
        (∑ i, (B k i : ℝ) * θ i) - b k := by
      simp only [mul_sub,Finset.sum_sub_distrib,correction,hR]
    rw [hs,Circle.exp_sub,←character_exp B θ k,hx,hbphase]
    simp
  have hyA : character A y = 1 := by
    rw [hA,character_mul,hyB]
    ext j
    simp [character]
  refine ⟨y,hyA,?_⟩
  let err := ‖Full.BulkTorus.difference (character A x) 1‖
  have he0 : 0 ≤ err := norm_nonneg _
  have ha (j : J) : |α j| ≤ K * err :=
    (harg (character A x j)).trans (mul_le_mul_of_nonneg_left
      (norm_le_pi_norm (Full.BulkTorus.difference (character A x) 1) j) hK.le)
  have hb (k : Fin r) : |b k| ≤ Cnorm * K * err := by
    calc
      _ ≤ ∑ j, |(C k j : ℝ) * α j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(C k j : ℝ)| * (K * err) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)
      _ = (∑ j, |(C k j : ℝ)|) * (K * err) := (Finset.sum_mul ..).symm
      _ ≤ Cnorm * K * err := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun j _ => abs_nonneg ((C l j : ℝ)))
            (Finset.mem_univ k)) (by positivity)
  have hcorr (i : I) : |correction i| ≤ Rnorm * Cnorm * K * err := by
    calc
      _ ≤ ∑ k, |R i k * b k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |R i k| * (Cnorm * K * err) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb k) (abs_nonneg _)
      _ = (∑ k, |R i k|) * (Cnorm * K * err) := (Finset.sum_mul ..).symm
      _ ≤ Rnorm * Cnorm * K * err := by
        have hh : (∑ k, |R i k|) ≤ Rnorm :=
          Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg (R j k))
            (Finset.mem_univ i)
        nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ Cnorm * K * err by positivity)]
  apply (pi_norm_le_iff_of_nonneg (by dsimp [L]; positivity)).mpr
  intro i
  change ‖(x i : ℂ) - (Circle.exp (θ i-correction i) : ℂ)‖ ≤ L * err
  rw [←Circle.exp_arg (x i)]
  have hh := hexp (θ i) (θ i-correction i)
  simp only [sub_sub_cancel] at hh
  exact (hh.trans (hcorr i)).trans (by dsimp [L]; nlinarith)

/-- The finite-torus metric estimate is derived by the manuscript's integer
basis and right-inverse construction, rather than assumed as a whole. -/
theorem finite_torus_error_bound
    (basis : IntegerRowBasis.{u}) (geometry : CircleMetricFacts)
    (characters : ContinuousCharacterClassification.{u}) :
    Full.BulkTorus.FiniteTorusErrorBound.{u} := by
  intro I J _ _ F hF
  obtain ⟨A,hA⟩ := characters F hF
  obtain ⟨L,hL,hh⟩ := integer_lattice_correction basis geometry A
  refine ⟨L,hL,?_⟩
  intro x
  obtain ⟨y,hy,hxy⟩ := hh x
  exact ⟨y,by rw [hA,hy],by simpa only [hA] using hxy⟩

end NonSymmetricDyson.Paper.BulkTorus
