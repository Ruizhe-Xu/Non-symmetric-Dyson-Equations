import Mathlib

/-! Concrete positive-edge typed words for the weighted-tree construction
in the previous corrected blueprint. Root removal and the unique-parent
parametrization below are equivalences of actual countable vertex types. -/
noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.TreeWords
universe u
variable {ι : Type u}

inductive Word (S : ι → ι → ℝ) : ι → Type u
  | nil (i : ι) : Word S i
  | cons {i j : ι} (edge : 0 < S i j) (tail : Word S j) : Word S i

namespace Word
variable {S : ι → ι → ℝ}

def depth {i : ι} : Word S i → ℕ
  | .nil _ => 0
  | .cons _ w => depth w + 1

def terminal {i : ι} : Word S i → ι
  | .nil i => i
  | .cons _ w => terminal w

abbrev Child {i : ι} (w : Word S i) := {j : ι // 0 < S (terminal w) j}

/-- Append one positive edge to the terminal end of a word. -/
def child {i : ι} : (w : Word S i) → Child w → Word S i
  | .nil i, j => .cons j.property (.nil j.val)
  | .cons h w, j => .cons h (child w j)

@[simp] theorem terminal_child {i : ι} (w : Word S i) (j : Child w) :
    terminal (child w j) = j.val := by
  induction w with
  | nil => rfl
  | cons h w ih => exact ih j

@[simp] theorem depth_child {i : ι} (w : Word S i) (j : Child w) :
    depth (child w j) = depth w + 1 := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [child,depth,ih]

@[simp] theorem child_ne_nil {i : ι} (w : Word S i) (j : Child w) :
    child w j ≠ .nil i := by
  intro h
  have hd := congrArg depth h
  simp [depth] at hd

/-- Prefixing the first edge embeds a complete forward subtree. -/
def consEmbedding {i j : ι} (h : 0 < S i j) : Word S j ↪ Word S i where
  toFun := .cons h
  inj' w v hEq := eq_of_heq (Word.cons.inj hEq).2

@[simp] theorem consEmbedding_apply {i j : ι} (h : 0 < S i j) (w : Word S j) :
    consEmbedding h w = .cons h w := rfl

/-- The first-edge decomposition identifies each forward branch with a
fresh copy of the tree of its terminal type. -/
def rootEquiv (S : ι → ι → ℝ) (i : ι) :
    Word S i ≃ Unit ⊕ (Σ j : {j : ι // 0 < S i j}, Word S j.val) where
  toFun
    | .nil _ => Sum.inl ()
    | .cons h w => Sum.inr ⟨⟨_,h⟩,w⟩
  invFun
    | .inl _ => .nil i
    | .inr ⟨j,w⟩ => .cons j.property w
  left_inv w := by cases w <;> rfl
  right_inv x := by rcases x with _ | ⟨j,w⟩ <;> rfl

/-- Every nonroot word has one immediate predecessor and one last edge. -/
theorem exists_child {i : ι} (v : Word S i) (hv : v ≠ .nil i) :
    ∃ w : Word S i, ∃ j : Child w, child w j = v := by
  induction v with
  | nil i => exact False.elim (hv rfl)
  | @cons i j h v ih =>
    by_cases hnil : v = .nil j
    · subst v
      exact ⟨.nil i, ⟨j,h⟩, rfl⟩
    · obtain ⟨w,k,hk⟩ := ih hnil
      exact ⟨.cons h w, k, by simp only [child,hk]⟩

private def first {i : ι} : Word S i → Option ι
  | .nil _ => none
  | @Word.cons _ _ i j _ _ => some j

/-- Distinct predecessor/last-edge pairs produce distinct vertices. -/
theorem child_injective {i : ι} :
    Function.Injective (fun p : Σ w : Word S i, Child w => child p.1 p.2) := by
  intro p q hpq
  rcases p with ⟨w,j⟩
  rcases q with ⟨v,k⟩
  induction w with
  | nil i =>
    cases v with
    | nil =>
      have h : j.val = k.val := congrArg terminal hpq
      have hj : j = k := Subtype.ext h
      subst k
      rfl
    | cons h v =>
      have hd := congrArg depth hpq
      simp [child,depth] at hd
  | @cons i t h w ih =>
    cases v with
    | nil =>
      have hd := congrArg depth hpq
      simp [child,depth] at hd
    | @cons _ s h' v =>
      have hh : t = s := by simpa only [child,first,Option.some.injEq] using congrArg first hpq
      subst s
      have hv : child w j = child v k := eq_of_heq (Word.cons.inj hpq).2
      have he := ih j v k hv
      cases he
      rfl

/-- Actual bijection from child incidences to the nonroot vertices. -/
def childrenEquiv (S : ι → ι → ℝ) (i : ι) :
    (Σ w : Word S i, Child w) ≃ {v : Word S i // v ≠ .nil i} :=
  Equiv.ofBijective (fun p => ⟨child p.1 p.2, child_ne_nil p.1 p.2⟩) ⟨
    fun p q h => child_injective (congrArg Subtype.val h), by
      rintro ⟨v,hv⟩
      obtain ⟨w,j,h⟩ := exists_child v hv
      exact ⟨⟨w,j⟩, Subtype.ext h⟩⟩

/-- Root plus all parent/child incidences enumerate the whole tree. -/
def treeEquiv (S : ι → ι → ℝ) (i : ι) :
    Unit ⊕ (Σ w : Word S i, Child w) ≃ Word S i := by
  classical
  let f : Unit ⊕ (Σ w : Word S i, Child w) → Word S i :=
    fun x => match x with | .inl _ => .nil i | .inr p => child p.1 p.2
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr q => exact False.elim (child_ne_nil q.1 q.2 h.symm)
    | inr p =>
      cases y with
      | inl y => exact False.elim (child_ne_nil p.1 p.2 h)
      | inr q => exact congrArg Sum.inr (child_injective h)
  · intro v
    by_cases hv : v = .nil i
    · exact ⟨.inl (),hv.symm⟩
    · obtain ⟨w,j,h⟩ := exists_child v hv
      exact ⟨.inr ⟨w,j⟩,h⟩

@[simp] theorem treeEquiv_root (S : ι → ι → ℝ) (i : ι) :
    treeEquiv S i (.inl ()) = .nil i := rfl

@[simp] theorem treeEquiv_child (S : ι → ι → ℝ) (i : ι)
    (w : Word S i) (j : Child w) : treeEquiv S i (.inr ⟨w,j⟩) = child w j := rfl

/-- The list of successive vertex types is a faithful countable encoding. -/
def letters {i : ι} : Word S i → List ι
  | .nil _ => []
  | @Word.cons _ _ i j _ w => j :: letters w

theorem letters_injective {i : ι} : Function.Injective (letters (S := S) (i := i)) := by
  intro w v h
  induction w with
  | nil i =>
    cases v with
    | nil => rfl
    | cons h' v => simp [letters] at h
  | @cons i j e w ih =>
    cases v with
    | nil => simp [letters] at h
    | @cons _ k e' v =>
      have hh : j = k ∧ letters w = letters v := by simpa [letters] using h
      rcases hh with ⟨rfl,ht⟩
      have hv := ih ht
      cases hv
      rfl

instance [Countable ι] (S : ι → ι → ℝ) (i : ι) : Countable (Word S i) :=
  Function.Injective.countable letters_injective

instance [Fintype ι] {i : ι} (w : Word S i) : Fintype (Child w) := by
  classical
  exact Subtype.fintype _

/-- The square-root weights are unchanged by deleting a first edge. -/
def edgeWeight {i : ι} (w : Word S i) (j : Child w) : ℝ :=
  Real.sqrt (S (terminal w) j.val)

@[simp] theorem edgeWeight_sq {i : ι} (w : Word S i) (j : Child w) :
    edgeWeight w j ^ 2 = S (terminal w) j.val := Real.sq_sqrt j.property.le

@[simp] theorem child_cons {i j : ι} (h : 0 < S i j)
    (w : Word S j) (k : Child w) : child (.cons h w) k = .cons h (child w k) := rfl

@[simp] theorem terminal_cons {i j : ι} (h : 0 < S i j) (w : Word S j) :
    terminal (.cons h w) = terminal w := rfl

@[simp] theorem edgeWeight_cons {i j : ι} (h : 0 < S i j)
    (w : Word S j) (k : Child w) : edgeWeight (.cons h w) k = edgeWeight w k := rfl


/-- The creation-operator row norm is exactly the original matrix row sum. -/
theorem child_square_sum [Fintype ι] (hS : ∀ i j, 0 ≤ S i j)
    {i : ι} (w : Word S i) :
    (∑ j : Child w, edgeWeight w j ^ 2) = ∑ j, S (terminal w) j := by
  classical
  simp_rw [edgeWeight_sq]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 0 < S (terminal w) j)
    (fun j => S (terminal w) j)]
  have hz : (∑ j : {j : ι // ¬0 < S (terminal w) j}, S (terminal w) j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact le_antisymm (le_of_not_gt j.property) (hS _ _)
  rw [hz,add_zero]

/-- The row bound used for the actual ℓ² creation operator. -/
theorem child_square_bound [Fintype ι] (hS : ∀ i j, 0 ≤ S i j)
    (R : ℝ) (hR : ∀ i, (∑ j, S i j) ≤ R) {i : ι} (w : Word S i) :
    (∑ j : Child w, edgeWeight w j ^ 2) ≤ R := by
  rw [child_square_sum hS]
  exact hR _

/-- The potential is inherited from the terminal type. -/
def potential (a : ι → ℝ) {i : ι} (w : Word S i) : ℝ := a (terminal w)

@[simp] theorem potential_cons (a : ι → ℝ) {i j : ι} (h : 0 < S i j) (w : Word S j) :
    potential a (.cons h w) = potential a w := rfl


end Word
end NonSymmetricDyson.Paper.TreeWords
