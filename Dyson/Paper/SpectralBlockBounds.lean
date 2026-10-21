import Dyson.Paper.SpectralResidual

noncomputable section
namespace NonSymmetricDyson.Paper.Spectral
open Full.Spectral
variable {ι : Type*} [Fintype ι]

/-- Original M,N and scalar block bounds after the exact Perron cancellation. -/
theorem coupling_block_bounds (E : End ι) (r : Vec ι) (l : Dual ι) (a : ℂ) :
    ‖l.comp (E.comp (complement r l))‖≤‖l‖*‖E‖*‖complement r l‖ ∧
    ‖complement r l (E r)‖≤‖complement r l‖*‖E‖*‖r‖ ∧
    ‖a+l (E r)‖≤‖a‖+‖l‖*‖E‖*‖r‖ := by
  refine ⟨?_,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans_eq (by ring))
  · exact ((complement r l).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (E.le_opNorm r) (norm_nonneg _)).trans_eq (by ring))
  · exact (norm_add_le _ _).trans (add_le_add_left
      ((l.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (E.le_opNorm r) (norm_nonneg _)).trans_eq (by ring))) _)

/-- The actual scalar Schur function differs quadratically from its affine
part. This is the precise estimate to which the generic Rouché argument applies. -/
theorem schur_quadratic_bound (A E : End ι) (r : Vec ι) (l : Dual ι) (a z : ℂ)
    (hnorm : l r=1) (hr : A r=a • r) (hl : ∀ x,l (A x)=a*l x)
    (J : ComplementResolvent (A+E) r l z) :
    ‖schurScalar (A+E) r l z J-(a+l (E r)-z)‖≤
      ‖l‖*‖E‖*‖J.inverse‖*‖complement r l‖*‖E‖*‖r‖ := by
  obtain ⟨hscalar,hN,hM⟩ := adapted_block_cancellation A E r l a hnorm hr hl
  have he : schurScalar (A+E) r l z J-(a+l (E r)-z)=
      -l (E (J.inverse (complement r l (E r)))) := by
    unfold schurScalar
    rw [hscalar,hN,hM _ (J.centered _)]
    ring
  rw [he,norm_neg]
  calc
    _ ≤ ‖l‖*‖E (J.inverse (complement r l (E r)))‖ := l.le_opNorm _
    _ ≤ ‖l‖*(‖E‖*(‖J.inverse‖*(‖complement r l‖*(‖E‖*‖r‖)))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (E.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (J.inverse.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply ((complement r l).le_opNorm _).trans
      exact mul_le_mul_of_nonneg_left (E.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

/-- The strict boundary comparison used by Rouché is proved internally.
The holomorphic zero-counting theorem itself remains general external analysis. -/
theorem schur_rouche_boundary_comparison (f : ℂ → ℂ) (a z : ℂ) (rho err : ℝ)
    (hz : ‖z‖=rho) (ha : ‖a‖<rho/2) (herr : err<rho/2)
    (hrem : ‖f z-(a-z)‖≤err) : ‖f z-(a-z)‖<‖a-z‖ := by
  have h := norm_sub_norm_le z a
  rw [hz,norm_sub_rev] at h
  linarith

end NonSymmetricDyson.Paper.Spectral
