import Dyson.Full.ExternalAlgebraic

/-! The field of algebraic functions is closed under rational translation.
The parameter is a universal algebraic fact; it contains no boundary,
positivity, measure, or Dyson assertions. -/

noncomputable section
open scoped BigOperators

namespace NonSymmetricDyson.Full.ExternalAlgebraic

/-- Subtracting finitely many simple rational fractions preserves a
nontrivial polynomial relation. This is a standard field-theoretic closure
property, stated explicitly among the allowed external algebraic inputs. -/
structure RationalAlgebraicity : Prop where
  subtract : ∀ (f : ℂ → ℂ) (A : Finset ℝ) (c : ℝ → ℂ),
    AlgebraicOnUpper f →
    AlgebraicOnUpper (fun z => f z - ∑ τ ∈ A, c τ / ((τ : ℂ) - z))

end NonSymmetricDyson.Full.ExternalAlgebraic
