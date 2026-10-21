import Dyson.Paper.SpectralBoundary

/-! The source's componentwise eigenvector and pairing nondegeneracy.
The proof uses actual Taylor approximants and the positive limiting frame. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace NonSymmetricDyson.Paper.Spectral
open Full Full.Spectral Full.Singularities Full.SingularSpectral Full.PerronContinuation
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def leftCoefficient (l : Dual ι) (i : ι) : ℂ := l (Pi.single i 1)

theorem leftCoefficient_real (l : ι → ℝ) (i : ι) :
    leftCoefficient (complexFunctional l) i=(l i:ℂ) := by
  unfold leftCoefficient
  rw [complexFunctional_apply]
  simp [Pi.single_apply,mul_ite]

theorem leftCoefficient_sub_bound (l t : Dual ι) (i : ι) :
    ‖leftCoefficient l i-leftCoefficient t i‖≤‖l-t‖ := by
  have h := (l-t).le_opNorm (Pi.single i (1:ℂ))
  simpa [leftCoefficient,Pi.norm_single] using h

/-- The coefficient norm is exactly the actual adjoint-left vector norm. -/
theorem adjointLeftVector_coordinate_norm (v : Dual ι) (i : ι) :
    ‖adjointLeftVector v i‖=‖leftCoefficient v i‖ := by
  have h := adjointLeftVector_inner v (WithLp.toLp 2 (Pi.single i (1:ℂ)))
  rw [PiLp.inner_apply] at h
  change (∑ j,(Pi.single i (1:ℂ) : ι → ℂ) j*star (adjointLeftVector v j))=
    v (Pi.single i 1) at h
  simp [Pi.single_apply,ite_mul] at h
  have hn := congrArg norm h
  simpa [leftCoefficient] using hn

/-- Explicit local continuity consequence. It bounds each vector component
and the left/right pairing by constants independent of the nearby point. -/
theorem spectral_lengths_of_close
    (r l : ι → ℝ) (t : Vec ι) (v : Dual ι)
    (b B e : ℝ) (hb : 0<b) (hB : 0≤B) (he : 0≤e)
    (hrlo : ∀ i,b≤r i) (hllo : ∀ i,b≤l i)
    (hrB : ‖(fun i => (r i:ℂ))‖≤B) (hlB : ‖complexFunctional l‖≤B)
    (hnorm : complexFunctional l (fun i => (r i:ℂ))=1)
    (htr : ‖t-(fun i => (r i:ℂ))‖≤e) (hvl : ‖v-complexFunctional l‖≤e)
    (heb : e≤b/2) (he1 : e≤1) (heB : e*(2*B+1)≤1/2) :
    (∀ i,b/2≤‖t i‖ ∧ ‖t i‖≤B+1) ∧
    (∀ i,b/2≤‖leftCoefficient v i‖ ∧ ‖leftCoefficient v i‖≤B+1) ∧
    1/2≤‖v t‖ ∧ ‖v t‖≤3/2 := by
  have htn : ‖t‖≤B+e := by
    have h := norm_sub_norm_le t (fun i => (r i:ℂ))
    linarith
  have hvn : ‖v‖≤B+e := by
    have h := norm_sub_norm_le v (complexFunctional l)
    linarith
  have hpair : ‖v t-1‖≤e*(2*B+1) := by
    have hid : v t-1=(v-complexFunctional l) t+
        complexFunctional l (t-(fun i => (r i:ℂ))) := by
      simp only [ContinuousLinearMap.sub_apply,map_sub,hnorm]
      ring
    rw [hid]
    calc
      _ ≤ ‖(v-complexFunctional l) t‖+‖complexFunctional l (t-(fun i => (r i:ℂ)))‖ := norm_add_le _ _
      _ ≤ e*(B+e)+B*e := by
        gcongr
        · exact ((v-complexFunctional l).le_opNorm _).trans (mul_le_mul hvl htn (norm_nonneg _) he)
        · exact ((complexFunctional l).le_opNorm _).trans (mul_le_mul hlB htr (norm_nonneg _) hB)
      _ ≤ _ := by nlinarith
  have hp : ‖v t-1‖≤1/2 := hpair.trans heB
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    have hd : ‖t i-(r i:ℂ)‖≤e := (norm_le_pi_norm (t-(fun j => (r j:ℂ))) i).trans htr
    have hri : ‖(r i:ℂ)‖=r i := by simp [abs_of_pos (hb.trans_le (hrlo i))]
    constructor
    · have h := norm_sub_norm_le (r i:ℂ) (t i)
      rw [norm_sub_rev,hri] at h
      linarith [hrlo i]
    · exact (norm_le_pi_norm t i).trans (by linarith)
  · intro i
    have hd := (leftCoefficient_sub_bound v (complexFunctional l) i).trans hvl
    rw [leftCoefficient_real] at hd
    have hli : ‖(l i:ℂ)‖=l i := by simp [abs_of_pos (hb.trans_le (hllo i))]
    constructor
    · have h := norm_sub_norm_le (l i:ℂ) (leftCoefficient v i)
      rw [norm_sub_rev,hli] at h
      linarith [hllo i]
    · have h := v.le_opNorm (Pi.single i (1:ℂ))
      have hh : ‖leftCoefficient v i‖≤‖v‖ := by simpa [leftCoefficient,Pi.norm_single] using h
      exact hh.trans (by linarith)
  · have h := norm_sub_norm_le (1:ℂ) (v t)
    rw [norm_one,norm_sub_rev] at h
    linarith
  · have h := norm_sub_norm_le (v t) (1:ℂ)
    rw [norm_one] at h
    linarith

/-- Uniform nondegeneracy from convergent Taylor approximants. This generic
finite-dimensional continuity lemma is proved here, not external spectral input. -/
theorem eventually_spectral_lengths {X : Type*} (L : Filter X)
    (r l : ι → ℝ) (hr : ∀ i,0<r i) (hl : ∀ i,0<l i)
    (hnorm : complexFunctional l (fun i => (r i:ℂ))=1)
    (R : X → Vec ι) (V : X → Dual ι) (err : X → ℝ)
    (hR : Tendsto R L (𝓝 (fun i => (r i:ℂ))))
    (hV : Tendsto V L (𝓝 (complexFunctional l))) (herr : Tendsto err L (𝓝 0))
    [Nonempty ι] :
    ∃ b B : ℝ,0<b ∧ 0<B ∧ ∀ᶠ x in L,
      ∀ t : Vec ι,∀ v : Dual ι,‖t-R x‖≤err x → ‖v-V x‖≤err x →
      (∀ i,b≤‖t i‖ ∧ ‖t i‖≤B) ∧
      (∀ i,b≤‖leftCoefficient v i‖ ∧ ‖leftCoefficient v i‖≤B) ∧
      b≤‖v t‖ ∧ ‖v t‖≤B := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun i => min (r i) (l i)) Finset.univ_nonempty
  let b₀ := min (r i) (l i)
  have hb₀ : 0<b₀ := lt_min (hr i) (hl i)
  have hrlo (j : ι) : b₀≤r j := (hi j (Finset.mem_univ j)).trans (min_le_left _ _)
  have hllo (j : ι) : b₀≤l j := (hi j (Finset.mem_univ j)).trans (min_le_right _ _)
  let B₀ := 1+‖(fun i => (r i:ℂ))‖+‖complexFunctional l‖
  have hB₀ : 0≤B₀ := by dsimp [B₀]; positivity
  let e := min (b₀/2) (min 1 ((2*(2*B₀+1))⁻¹))
  have he : 0<e := by dsimp [e]; positivity
  have heB : e*(2*B₀+1)≤1/2 := by
    have heq : (2*(2*B₀+1))⁻¹*(2*B₀+1)=1/2 := by field_simp
    exact (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by positivity)).trans_eq heq
  have hRerr : Tendsto (fun x => err x+‖R x-(fun i => (r i:ℂ))‖) L (𝓝 0) := by
    simpa using herr.add ((hR.sub (tendsto_const_nhds (x := (fun i => (r i:ℂ))))).norm)
  have hVerr : Tendsto (fun x => err x+‖V x-complexFunctional l‖) L (𝓝 0) := by
    simpa using herr.add ((hV.sub (tendsto_const_nhds (x := complexFunctional l))).norm)
  refine ⟨min (b₀/2) (1/2),B₀+2,lt_min (half_pos hb₀) (by norm_num),by positivity,?_⟩
  filter_upwards [hRerr.eventually_le_const he,hVerr.eventually_le_const he] with x hRx hVx
  intro t v ht hv
  have htr : ‖t-(fun i => (r i:ℂ))‖≤e := by
    exact ((norm_sub_le_norm_sub_add_norm_sub t (R x) _).trans (add_le_add_right ht _)).trans hRx
  have hvl : ‖v-complexFunctional l‖≤e := by
    exact ((norm_sub_le_norm_sub_add_norm_sub v (V x) _).trans (add_le_add_right hv _)).trans hVx
  obtain ⟨htl,hvl,hpl,hpu⟩ := spectral_lengths_of_close r l t v b₀ B₀ e hb₀ hB₀ he.le
    hrlo hllo (by dsimp [B₀]; linarith [norm_nonneg (complexFunctional l)])
    (by dsimp [B₀]; linarith [norm_nonneg (fun i => (r i:ℂ))]) hnorm htr hvl
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)) heB
  exact ⟨fun i => ⟨(min_le_left _ _).trans (htl i).1,by linarith [(htl i).2]⟩,
    fun i => ⟨(min_le_left _ _).trans (hvl i).1,by linarith [(hvl i).2]⟩,
    (min_le_right _ _).trans hpl,by linarith⟩

end NonSymmetricDyson.Paper.Spectral
