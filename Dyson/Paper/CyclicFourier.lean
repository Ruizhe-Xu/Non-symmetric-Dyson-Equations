import Dyson.Full.CyclicGeneral

/-! The appendix's Fourier route: the displayed vectors form a genuine
orthonormal basis, and the cyclic stability operator is unitarily diagonal. -/
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace NonSymmetricDyson.Paper.CyclicFourier
open Full.CyclicGeneral
variable (d : ℕ) [NeZero d]

def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

theorem omega_primitive : IsPrimitiveRoot (omega d) d :=
  Complex.isPrimitiveRoot_exp d (NeZero.ne d)

def mode (ζ : ℂ) (k : Fin d) : Space d :=
  ((Real.sqrt d : ℂ)⁻¹) • WithLp.toLp 2 (eigenvector d (ζ^k.val))

theorem mode_norm (ζ : ℂ) (hζ : ‖ζ‖=1) (k : Fin d) : ‖mode d ζ k‖=1 := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have he : ‖WithLp.toLp 2 (eigenvector d (ζ^k.val))‖^2=(d : ℝ) := by
    simp [EuclideanSpace.norm_sq_eq,eigenvector,norm_pow,hζ]
  have hn : ‖WithLp.toLp 2 (eigenvector d (ζ^k.val))‖=Real.sqrt d := by
    nlinarith [Real.sq_sqrt hd.le,norm_nonneg (WithLp.toLp 2 (eigenvector d (ζ^k.val))),
      Real.sqrt_nonneg (d : ℝ)]
  rw [mode,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),hn,inv_mul_cancel₀ (Real.sqrt_pos.mpr hd).ne']

theorem mode_eigen (ζ : ℂ) (hζ : ζ^d=1) (k : Fin d) :
    shift₂ d (mode d ζ k)=(ζ^k.val) • mode d ζ k := by
  have hk : (ζ^k.val)^d=1 := by rw [← pow_mul,mul_comm k.val d,pow_mul,hζ,one_pow]
  rw [mode,map_smul,shift₂_eigenvector d _ hk,smul_comm]

def shiftIsometry : Space d →ₗᵢ[ℂ] Space d :=
  { (shift₂ d).toLinearMap with norm_map' := shift₂_isometry d }

theorem modes_orthogonal (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d)
    {j k : Fin d} (hjk : j≠k) : ⟪mode d ζ j,mode d ζ k⟫_ℂ=0 := by
  have he := (shiftIsometry d).inner_map_map (mode d ζ j) (mode d ζ k)
  change ⟪shift₂ d (mode d ζ j),shift₂ d (mode d ζ k)⟫_ℂ = _ at he
  rw [mode_eigen d ζ hζ.pow_eq_one,mode_eigen d ζ hζ.pow_eq_one,
    inner_smul_left,inner_smul_right] at he
  have hu : ζ^j.val * (starRingEnd ℂ) (ζ^j.val)=1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm]
    simp [norm_pow,hζ.norm'_eq_one (NeZero.ne d)]
  have hd : ζ^j.val≠ζ^k.val := fun h => hjk (Fin.ext (hζ.pow_inj j.isLt k.isLt h))
  have hh := congrArg (fun x : ℂ => ζ^j.val*x) he
  have hh' : (ζ^k.val-ζ^j.val)*⟪mode d ζ j,mode d ζ k⟫_ℂ=0 := by
    calc
      _ = (ζ^j.val*(starRingEnd ℂ) (ζ^j.val))*(ζ^k.val*⟪mode d ζ j,mode d ζ k⟫_ℂ) -
          ζ^j.val*⟪mode d ζ j,mode d ζ k⟫_ℂ := by rw [hu]; ring
      _ = 0 := by linear_combination hh
  exact (mul_eq_zero.mp hh').resolve_left (sub_ne_zero.mpr hd.symm)

theorem modes_orthonormal (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) :
    Orthonormal ℂ (mode d ζ) := by
  exact ⟨mode_norm d ζ (hζ.norm'_eq_one (NeZero.ne d)),fun j k hjk => modes_orthogonal d ζ hζ hjk⟩

def basis (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) : OrthonormalBasis (Fin d) ℂ (Space d) :=
  (basisOfOrthonormalOfCardEqFinrank (modes_orthonormal d ζ hζ) (by simp)).toOrthonormalBasis
    (by simpa using modes_orthonormal d ζ hζ)

@[simp] theorem basis_apply (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (k : Fin d) :
    basis d ζ hζ k=mode d ζ k := by simp [basis]

theorem stability_eigen (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ) (k : Fin d) :
    (1-q • shift₂ d) (basis d ζ hζ k)=(1-q*ζ^k.val) • basis d ζ hζ k := by
  rw [basis_apply]
  change mode d ζ k - q • shift₂ d (mode d ζ k) = _
  rw [mode_eigen d ζ hζ.pow_eq_one]
  module

/-- Coordinates in the actual Fourier orthonormal basis diagonalize the
operator, so this is a unitary, rather than merely algebraic, diagonalization. -/
theorem unitary_diagonalization (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (q : ℂ) (x : Space d) :
    (basis d ζ hζ).repr ((1-q • shift₂ d) x) =
      WithLp.toLp 2 (fun k => (1-q*ζ^k.val)*((basis d ζ hζ).repr x k)) := by
  classical
  have hx := (basis d ζ hζ).sum_repr x
  conv_lhs => rw [← hx]
  simp only [map_sum,map_smul,stability_eigen,smul_smul]
  ext k
  simp only [← basis_apply d ζ hζ, OrthonormalBasis.repr_self]
  change PiLp.projₗ (𝕜 := ℂ) (β := fun _ : Fin d => ℂ) 2 k
    (∑ j, (((basis d ζ hζ).repr x j)*(1-q*ζ^j.val)) • EuclideanSpace.single j (1:ℂ)) = _
  rw [map_sum]
  simp [mul_comm]

end NonSymmetricDyson.Paper.CyclicFourier
