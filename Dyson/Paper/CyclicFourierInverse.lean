import Dyson.Paper.CyclicFourier
import Dyson.Full.CyclicTaylor

noncomputable section
open scoped BigOperators
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full.CyclicGeneral
variable (d : ℕ) [NeZero d]

/-- An actual inverse acts diagonally in the orthonormal Fourier basis. -/
theorem inverse_on_mode (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ)
    (T : Space d →L[ℂ] Space d)
    (hT : ∀x,T ((1-q • shift₂ d) x)=x)
    (k : Fin d) (hk : 1-q*ζ^k.val≠0) :
    T (basis d ζ hζ k)=(1-q*ζ^k.val)⁻¹ • basis d ζ hζ k := by
  have h := hT (basis d ζ hζ k)
  rw [stability_eigen,map_smul] at h
  have hh := congrArg (fun x : Space d => (1-q*ζ^k.val)⁻¹ • x) h
  simpa only [smul_smul,inv_mul_cancel₀ hk,one_smul] using hh

theorem inverse_mode_lower (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ)
    (T : Space d →L[ℂ] Space d) (hT : ∀x,T ((1-q • shift₂ d) x)=x)
    (k : Fin d) (hk : 1-q*ζ^k.val≠0) : ‖1-q*ζ^k.val‖⁻¹≤‖T‖ := by
  have h := T.le_opNorm (basis d ζ hζ k)
  rw [inverse_on_mode d ζ hζ q T hT k hk,norm_smul,norm_inv,
    (basis d ζ hζ).norm_eq_one,mul_one,mul_one] at h
  exact h

/-- Uniform mode-wise bounds control the inverse through the Fourier basis.
The harmless factor d is explicit; all constants are independent of η. -/
theorem inverse_fourier_upper (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ)
    (T : Space d →L[ℂ] Space d) (hT : ∀x,T ((1-q • shift₂ d) x)=x)
    (B : ℝ) (hB : 0≤B) (hβ : ∀k : Fin d,1-q*ζ^k.val≠0)
    (hbound : ∀k : Fin d,‖1-q*ζ^k.val‖⁻¹≤B) : ‖T‖≤d*B := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hx := (basis d ζ hζ).sum_repr x
  calc
    ‖T x‖=‖∑ k : Fin d, ((basis d ζ hζ).repr x k) •
        ((1-q*ζ^k.val)⁻¹ • basis d ζ hζ k)‖ := by
      conv_lhs => rw [← hx]
      simp only [map_sum,map_smul,inverse_on_mode d ζ hζ q T hT _ (hβ _)]
    _ ≤ ∑ k : Fin d, ‖((basis d ζ hζ).repr x k) •
        ((1-q*ζ^k.val)⁻¹ • basis d ζ hζ k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin d, B*‖x‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul,norm_smul,norm_inv,(basis d ζ hζ).norm_eq_one,mul_one]
      have hc : ‖(basis d ζ hζ).repr x k‖≤‖x‖ := by
        calc
          _ ≤ ‖(basis d ζ hζ).repr x‖ := PiLp.norm_apply_le _ k
          _ = ‖x‖ := (basis d ζ hζ).repr.norm_map x
      nlinarith [mul_le_mul hc (hbound k) (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg x)]
    _ = (d*B)*‖x‖ := by simp; ring

def singularIndex (hd : 3≤d) : Fin d := ⟨d-2,by omega⟩

theorem singular_mode_power (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (hd : 3≤d) :
    ζ^2*ζ^(singularIndex d hd).val=1 := by
  rw [singularIndex,← pow_add,show 2+(d-2)=d by omega,hζ.pow_eq_one]

/-- Exactly the manuscript's mode k=d−2 vanishes at m=ω. -/
theorem unique_singular_mode (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (hd : 3≤d) (k : Fin d) :
    1-ζ^2*ζ^k.val=0 ↔ k=singularIndex d hd := by
  have hn : ζ^2≠0 := pow_ne_zero _ (hζ.ne_zero (NeZero.ne d))
  constructor
  · intro h
    have he : ζ^k.val=ζ^(singularIndex d hd).val :=
      mul_left_cancel₀ hn ((sub_eq_zero.mp h).symm.trans (singular_mode_power d ζ hζ hd).symm)
    exact Fin.ext (hζ.pow_inj k.isLt (singularIndex d hd).isLt he)
  · rintro rfl
    rw [singular_mode_power d ζ hζ hd,sub_self]

end NonSymmetricDyson.Paper.CyclicFourier
