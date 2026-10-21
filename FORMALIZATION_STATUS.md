# Formalization and verification status

The formalization follows the revised manuscript `source/main-article-1014.tex`. All clauses of the seven main results, the named auxiliary results, and the appendix have corresponding Lean statements. The proof status is **conditional on the general external mathematical arguments** catalogued in [EXTERNAL_ARGUMENTS.md](EXTERNAL_ARGUMENTS.md); the two required quantifier clarifications are given below.

## Inventory in the supplied release

The original release reported the following outcomes; they should not be mistaken for a fresh execution of the streamlined distribution.

| Item | Source-release record |
|---|---:|
| Labeled manuscript results | 23: seven main theorems, fourteen internal auxiliary results, and two explicitly cited classical Frobenius/cyclic-decomposition results |
| Manuscript proof blocks mapped to the formalization | 20 |
| Paper-facing modules and named declarations/aliases | 112 modules and 563 declarations |
| Full project | 315 Lean modules and 1,916 named theorem/lemma/alias declarations |
| Lean source lines | 45,678 |
| Selected proof routes separately audited | 14 |
| Pinned Lean compiler | 4.24.0 |

According to the original verification record, the full sources passed actual compiler and source-hash checks, theorem-type audits, and transitive global-axiom checks, using only `propext`, `Classical.choice`, and `Quot.sound`. No project-added `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` was recorded. The separate proof-route checks confirmed that specified arguments were used in selected final endpoints.

Fresh results can be produced with `lake build` and `python3 scripts/verify.py`, or downloaded from a completed GitHub Actions run. The verification script regenerates its reports in `validation/`; historical logs have intentionally been omitted from this minimal repository.

## Fidelity and necessary clarifications

The paper-facing entry points retain the Euclidean support constant in M1, compact intervals in M4, Sym/NB model restrictions in M5 and M6, the one-sided cusp bound in M6, and the NB model with `a = 0` in M7. Stronger results in the old reusable backend do not substitute for the manuscript's actual statements.

1. **Fixed anchor before constants.** In M7, `c₀`, the implicit edge/cusp constants, and the neighborhood may depend on a previously fixed positive anchor `η₀` and the spectral region. A bound uniform as `η₀ → 0` fails because another zero-residual branch exists in an actual non-backtracking model on `K₄`; this obstruction has a Lean proof.
2. **A possibly smaller origin neighborhood.** The bipartite-origin statement allows a radius `0 < r ≤ ε` inside a prescribed neighborhood. The bounds hold on the smaller closed upper half-disk, including nonzero real-axis points. The original argument itself needs this radius reduction.

[`source/main-article-1014.tex`](source/main-article-1014.tex) preserves the supplied source, while [`source/main-article-1014.formalized.tex`](source/main-article-1014.formalized.tex) records these clarifications and background corrections: the universal cover of a finite tree need not be infinite, and reducible blocks may include zero singleton components with complex parameter-dependent forcing.

## Proof strategy and scope

The paper-facing development connects shortest-path comparison, differentiation under the Stieltjes integral, cyclic-class Fourier/Doeblin contraction, equality in Jensen's inequality and Sym/NB nondegeneracy, integer-lattice phase correction, Poisson profiles and inverse estimates, nonlinear residuals, continuous branch selection, and the appendix's Fourier diagonalization. The actual tree operator and Schur construction follow a corrected proof blueprint.

Some analytic normal-form principles, scalar root results, and generic spectral perturbation theorems are explicit external inputs. Some reusable backend arguments employ mathematically equivalent rewrites or a corrected-blueprint route. See [FIDELITY_REVIEW.md](FIDELITY_REVIEW.md): this does not assert that every displayed formula in the manuscript has been given its own separate Lean theorem.

**No `sorry` is not equivalent to no mathematical assumptions.** The theorem parameters are not global axioms and therefore do not appear in `#print axioms`. The complete generated signatures and assumption list must be consulted together when evaluating proof scope.
