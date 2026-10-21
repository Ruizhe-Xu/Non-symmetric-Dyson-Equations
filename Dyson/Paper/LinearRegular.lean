import Dyson.Full.MainLinearExteriorModel
import Dyson.Full.StrictBulkEndpoints
import Dyson.Paper.BulkStability
import Dyson.Paper.BulkOrigin

/-! The literal off-support and strict-bulk clauses of revised M6.
The off-support clause requires no Sym/NB hypothesis.  Symmetric clauses
below require the actual matrix symmetry, and NB clauses name the base graph. -/
noncomputable section
open Set
namespace NonSymmetricDyson.Paper.Linear
open Full
universe u
variable {V : Type u} [Fintype V]

alias off_support := OffSupport.main_theorem_six_exterior_model

theorem symmetric_bulk [Nonempty V]
    (ext : Foundations.ExternalStieltjesTheory V)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (S : Matrix V V ℝ) (a : V → ℝ) (hS : ∀i j,0≤S i j)
    (hc : Resonance.StronglyConnected (fun i j => S i j≠0))
    (hsym : ∀i j,S i j=S j i)
    (hstable : (¬∃part : Set V,BulkGraph.IsBipartition (E := fun i j => S i j≠0) part) ∨
      ¬∃t : ℝ,∀i,a i=t)
    (i : V) (ε : ℝ) (hε : 0<ε) :
    let m := GlobalWellPosedness.solution S a hS
    ∃c C : ℝ,0<c ∧ 0<C ∧ ∀z : ℂ,z.re∈StrictBulkModel.energySet m i ε → ∀hz : 0<z.im,
      c≤StrictBulkModel.inverseNorm S a hS z hz ∧ StrictBulkModel.inverseNorm S a hS z hz≤C := by
  exact StrictBulkModel.symmetric_linear ext algebraic puiseux S a hS hc
    (fun i j hij => by rwa [←hsym i j]) hstable i ε hε

theorem symmetric_exceptional_bulk [Nonempty V]
    (ext : Foundations.ExternalStieltjesTheory V)
    (algebraic : ExternalAlgebraic.JacobianAlgebraicity (ι := V))
    (puiseux : ExternalAlgebraic.ConvergentPuiseuxTheory)
    (perron : BulkPerron.PerronLeftAndSimple.{u})
    (S : Matrix V V ℝ) (hS : ∀i j,0≤S i j)
    (hc : Resonance.StronglyConnected (fun i j => S i j≠0))
    (hsym : ∀i j,S i j=S j i)
    (part : Set V) (hp : BulkGraph.IsBipartition (E := fun i j => S i j≠0) part)
    (a : ℝ) (i : V) (ε : ℝ) (hε : 0<ε) :
    let m := GlobalWellPosedness.solution S (fun _ => a) hS
    ∃c C : ℝ,0<c ∧ 0<C ∧ ∀z : ℂ,z.re∈StrictBulkModel.energySet m i ε → ∀hz : 0<z.im,
      c*max 1 ‖z-(a:ℂ)‖⁻¹≤StrictBulkModel.inverseNorm S (fun _ => a) hS z hz ∧
      StrictBulkModel.inverseNorm S (fun _ => a) hS z hz≤C*max 1 ‖z-(a:ℂ)‖⁻¹ := by
  exact StrictBulkModel.symmetric_exceptional ext algebraic puiseux perron S hS hc
    (fun i j hij => by rwa [←hsym i j]) part hp a i ε hε

alias nonbacktracking_bulk := StrictBulkModel.NB.linear
alias nonbacktracking_exceptional_bulk := StrictBulkModel.NB.exceptional

end NonSymmetricDyson.Paper.Linear
