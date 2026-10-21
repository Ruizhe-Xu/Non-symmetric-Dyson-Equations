import Dyson.Full.ExternalSpectral

/-! Original Step 2: exact adapted coordinates and scalar Schur reduction.
These are arbitrary complex operators, not a spectral conclusion postulated
for the Dyson matrix. -/
noncomputable section
namespace NonSymmetricDyson.Paper.Spectral
open Full.Spectral
variable {ι : Type*} [Fintype ι]

def complement (r : Vec ι) (l : Dual ι) : End ι :=
  ContinuousLinearMap.id ℂ (Vec ι)-l.smulRight r

@[simp] theorem complement_apply (r : Vec ι) (l : Dual ι) (x : Vec ι) :
    complement r l x=x-l x • r := rfl

theorem complement_centered (r : Vec ι) (l : Dual ι) (h : l r=1) (x : Vec ι) :
    l (complement r l x)=0 := by simp [complement_apply,h]

def adaptedCoordinates (r : Vec ι) (l : Dual ι) (h : l r=1) :
    Vec ι ≃ₗ[ℂ] ℂ × LinearMap.ker l.toLinearMap where
  toFun x := (l x,⟨complement r l x,complement_centered r l h x⟩)
  invFun y := y.1 • r+y.2
  left_inv x := by simp [complement_apply]
  right_inv y := by
    rcases y with ⟨a,y⟩
    have hy : l (y:Vec ι)=0 := y.property
    apply Prod.ext
    · simp [h,hy]
    · apply Subtype.ext
      simp [complement_apply,h,hy]
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change complement r l (x+y)=complement r l x+complement r l y
      exact map_add _ _ _
  map_smul' a x := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

/-- Both block equations are the actual conjugated eigenvalue equation. -/
theorem block_eigen_equation (A : End ι) (r : Vec ι) (l : Dual ι)
    (h : l r=1) (z a : ℂ) (y : Vec ι) (hy : l y=0) :
    A (a • r+y)=z • (a • r+y) ↔
      (l (A r)-z)*a+l (A y)=0 ∧
      a • complement r l (A r)+complement r l (A y)-z • y=0 := by
  have he : ∀ x : Vec ι,x=l x • r+complement r l x := by intro x; simp
  constructor
  · intro hx
    constructor
    · have hh := congrArg l hx
      simp only [map_add,map_smul,h,hy,smul_eq_mul,mul_one,mul_zero,add_zero] at hh
      linear_combination hh
    · have hh := congrArg (complement r l) hx
      have hr : complement r l r=0 := by simp [h]
      have hyr : complement r l y=y := by simp [hy]
      simp only [map_add,map_smul,hr,hyr,smul_zero,zero_add] at hh
      exact sub_eq_zero.mpr hh
  · rintro ⟨ha,hyA⟩
    have hp : complement r l (A (a • r+y))=z • y := by
      simp only [map_add,map_smul]
      exact sub_eq_zero.mp hyA
    have hl : l (A (a • r+y))=z*a := by
      simp only [map_add,map_smul,smul_eq_mul]
      linear_combination ha
    rw [he (A (a • r+y)),hl,hp,smul_add,smul_smul]

/-- A resolvent of the complementary block, represented on the whole space
by extension with zero on the scalar coordinate. -/
structure ComplementResolvent (A : End ι) (r : Vec ι) (l : Dual ι) (z : ℂ) where
  inverse : End ι
  centered : ∀ x,l (inverse x)=0
  right : ∀ x,l x=0 → complement r l (A (inverse x))-z • inverse x=x
  left : ∀ x,l x=0 → inverse (complement r l (A x)-z • x)=x

def schurScalar (A : End ι) (r : Vec ι) (l : Dual ι) (z : ℂ)
    (J : ComplementResolvent A r l z) : ℂ :=
  l (A r)-z-l (A (J.inverse (complement r l (A r))))

/-- Original scalar Schur equation, including the nonzero scalar coordinate
argument often hidden in the informal derivation. -/
theorem eigenvalue_iff_schur_zero (A : End ι) (r : Vec ι) (l : Dual ι)
    (h : l r=1) (z : ℂ) (J : ComplementResolvent A r l z) :
    (∃ x : Vec ι,x≠0 ∧ A x=z • x) ↔ schurScalar A r l z J=0 := by
  constructor
  · rintro ⟨x,hx,heig⟩
    let a := l x
    let y := complement r l x
    have hy : l y=0 := complement_centered r l h x
    have hxcoord : x=a • r+y := by simp [a,y]
    obtain ⟨ha,hY⟩ := (block_eigen_equation A r l h z a y hy).mp (by rwa [← hxcoord])
    have hj : y=-a • J.inverse (complement r l (A r)) := by
      have he : complement r l (A y)-z • y=-a • complement r l (A r) := by
        rw [neg_smul]
        apply eq_neg_of_add_eq_zero_left
        linear_combination hY
      have hh := congrArg J.inverse he
      rw [J.left y hy,map_smul] at hh
      exact hh
    have ha0 : a≠0 := by
      intro hz
      rw [hz,neg_zero,zero_smul] at hj
      exact hx (by simp [hxcoord,hz,hj])
    have hs : schurScalar A r l z J*a=0 := by
      rw [hj,map_smul,map_smul,smul_eq_mul] at ha
      change (l (A r)-z-l (A (J.inverse (complement r l (A r)))))*a=0
      linear_combination ha
    exact (mul_eq_zero.mp hs).resolve_right ha0
  · intro hs
    let y := -J.inverse (complement r l (A r))
    have hy : l y=0 := by simp [y,J.centered]
    have hn : r+y≠0 := by
      intro hz
      have hh := congrArg l hz
      simp [h,hy] at hh
    refine ⟨r+y,hn,?_⟩
    have hb := (block_eigen_equation A r l h z 1 y hy)
    simp only [one_smul] at hb
    apply hb.mpr
    constructor
    · change (l (A r)-z)*1+l (A (-J.inverse (complement r l (A r))))=0
      simpa only [mul_one,map_neg,sub_eq_add_neg] using hs
    · have hh := J.right (complement r l (A r)) (complement_centered r l h (A r))
      simp only [y,map_neg,smul_neg]
      linear_combination -hh

end NonSymmetricDyson.Paper.Spectral
