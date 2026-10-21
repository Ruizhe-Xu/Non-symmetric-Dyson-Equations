# Fidelity to the manuscript, corrections, and external proof boundaries

This formalization corresponds to the supplied 5,981-line manuscript in [`source/main-article-1014.tex`](source/main-article-1014.tex). Its paper-facing import is [`Dyson/Paper.lean`](Dyson/Paper.lean); see [PAPER_ENTRYPOINTS.md](PAPER_ENTRYPOINTS.md) for the main declaration names and [CORRESPONDENCE.md](CORRESPONDENCE.md) for the 23 labeled manuscript results. The exact mathematical strength of a result is determined by its Lean declaration, including every explicit hypothesis. Fresh full signatures can be generated with `python3 scripts/verify.py` and inspected in `validation/theorem_signatures.log`.

## Statements retained from the manuscript

- **M1.** The results concern arbitrary finite nonnegative matrices. They retain the unique upper-half-plane solution, analyticity, probability representation, and the manuscript's support-radius expression `|a|₂ + 2√‖S‖∞`. The proof in `FoundationsTree.tree_existence_and_uniqueness` uses a concrete weighted word tree, an actual ℓ² Jacobi operator, and its spectral measure, following the corrected blueprint. The earlier extension argument remains only as a compatible backend; it does not replace this tree-based proof.
- **M2.** The construction uses actual probability measures, atoms of strictly positive mass, pole subtraction, and boundary density limits that may be infinite. The common regular support is a finite union of disjoint open intervals. The atom formula has an explicit dominated-convergence argument.
- **M3 and M4.** M3 retains closed intervals, possibly unbounded, and all positive heights. Shortest-path comparison and the positive-polynomial comparison with a unit term are connected to the final statement. M4 uses compact intervals and two-point Hölder bounds on closed strips, with actual differentiation under the integral, upper-half-plane Lipschitz control, and finite compact coverings.
- **M5.** The exact Sym/NB model restrictions are retained: a stronger nondegeneracy theorem for arbitrary nonnegative matrices in the old backend is not silently substituted. Edges and cusps are defined using the shape of the actual support and related to incident interval endpoints. Positive leading coefficients, second-order errors, and zero density outside a regular edge are explicit.
- **M6.** The formal statements cover general off-support estimates, Sym/NB edges and cusps, ordinary strict bulk, and exceptional bipartite constant-potential cases. Edge estimates have the manuscript's two-sided power `1/2`; cusps yield only its one-sided upper bound with power `2/3`. All estimates use Euclidean norms of actual inverse operators and cover all positive imaginary heights.
- **M7.** The statements keep the NB setting with `a = 0`, the actual nonlinear residual, vertex reconstruction and balance quantities, genuine continuous solution paths, and any previously prescribed positive anchor. Physical-root selection and nonlinear stability are not simply assumed as external inputs.
- **Appendix.** The cyclic example covers arbitrary `d ≥ 3`, the actual resonant energy, and the small-height expansion. Its internal arguments include an explicit orthonormal Fourier basis, unitary diagonalization, and separation of singular and nonsingular modes.

Parentheses denoting coordinate sums in the source are interpreted the same way in Lean. When the paper-facing Perron statements involve specific coefficients, the *same* left/right eigenvectors have normalizations `Σ l r = 1` and `‖r‖₂ = 1`, rather than merely establishing that some normalization exists. Phase-reversal conventions, the relation between `rootRadius` and ordinary powers, and conversions of finite-dimensional norms are linked by explicit identities or estimates.

## Required clarifications of the mathematical statement

The supplied manuscript remains unmodified in `source/main-article-1014.tex`. The file `source/main-article-1014.formalized.tex` contains a minimally clarified version. For a line-level comparison one may use `diff -u source/main-article-1014.tex source/main-article-1014.formalized.tex`.

Two clarifications affect the quantifiers in the published mathematical estimates:

1. **Choose the anchor before the constants.** In M7, `c₀`, the implicit edge/cusp constants, and the neighborhood may depend on a previously fixed `η₀ > 0` and on the spectral region. If the original wording were interpreted as uniform in `η₀ → 0`, another exact zero-residual branch of the non-backtracking model on `K₄` would contradict that interpretation. `Paper.AnchorObstruction.actual_nb_anchor_obstruction` formalizes this mechanism.
2. **Shrink the origin neighborhood if necessary.** The bipartite-origin theorem gives two-sided inverse estimates on some `0 < r ≤ ε` contained in the initially prescribed bounded neighborhood. The original proof uses the same reduction; it cannot exclude other singular points throughout an arbitrary original `ε`. The conclusion covers the smaller *closed upper half-disk*, including its nonzero real boundary.

Two background statements are also clarified. The universal cover of a finite tree is again that finite tree, so a universal cover is not always infinite. For reducible matrices, strongly connected component blocks can be zero singleton blocks, and later blocks produce a generally *complex*, spectral-parameter-dependent effective forcing. The block algebra does not permit unconditional recursive reuse of every theorem formulated only for real potentials.

Corrections already present in the source concerning the identity term, Sym/NB restrictions, `a = 0`, and the restricted inverse at a singular boundary are kept. These assumptions are not dropped and the source conclusions are not silently strengthened.

## Paper arguments versus corrected-blueprint arguments

This development is not a renaming of older strengthened theorems. Its main proof paths and explicitly identified alternatives are as follows.

| Part | Route actually used |
|---|---|
| M1 | Concrete weighted word tree from the corrected blueprint → actual ℓ² creation and adjoint operators → self-adjoint Jacobi operator and norm bounds → internal Schur elimination → general spectral measure theorem → identification of the canonical Dyson solution. |
| Projected inverse for Perron/Markov operators | Manuscript's cyclic-class masses, Fourier decomposition, Doeblin contraction, eventual positivity on fixed support, and weighted orthogonal decomposition. The final projected inverse actually depends on the new proof chain. |
| Spectral perturbation | Actual Schur coordinates, characteristic equations, Dyson-specific coefficients, and boundary quotient interpretation are internal. Generic finite-dimensional analytic spectral perturbation, Rouché, and Taylor consequences are explicit external inputs. |
| Sym/NB nondegeneracy | Jensen equality, alternating signs in the symmetric setting, third-neighbor and terminal-potential constraints for NB, and the constant-potential reflection contradiction follow the manuscript. The new endpoints do not invoke the old alternative Möbius-based proof. |
| Cubic equation and Hölder estimates | The normalized `Θ`, `σ`, `ψ`, and error terms are computed from the same actual model data. Local analytic normal forms and root-sector results use general analytic principles from the corrected blueprint rather than claiming each such general theorem is internally formalized. |
| Graph phase and quantitative bulk | Phase propagation and integer-lattice correction are retained. Some principal-argument formulas are expressed through equivalent complex-product or variance identities; cycle generation uses an established edge/gauge character description with the same kernel. |
| M6 edges/cusps | Actual M5 asymptotics → local measure → Poisson integration including distant mass and atoms → Perron `δ` → manuscript's `β` expansion → norms of actual inverses → bounds at all positive heights. A monomial degenerate-inverse shortcut is not substituted. |
| Final globalization for strict bulk in M6 | The quantitative bulk and origin results are both separately proved. The public strict-bulk endpoint reuses a checked compact-kernel-exclusion/high-height-contraction globalization backend rather than invoking the quantitative theorem directly. This fallback is disclosed explicitly. |
| M7 | Actual residual, first and second derivatives of `W` and mixed errors, scalar root separation, anchoring, and connected-component selection. The bipartite balance assertion is assembled with an equivalent coercive augmented-operator argument. |
| Appendix | Manuscript's Fourier-mode decomposition and algebraic Taylor argument. The old finite geometric-series inverse is not treated as the new proof. |
| Signed Jacobi / NB application | Uses the actual real signed weights `b` in creation/adjoint operators, internal Schur elimination producing `b²`, and the actual NB forward Green-function recurrence; it does not begin by replacing `b` with `|b|`. |

For M2, the finite singular set is proved from local Puiseux isolation and a finite cover of compact support; propagation of zero imaginary part for the common regular support also follows actual support edges. The existence of a stand-alone intermediate lemma is not treated as proof that the final endpoint uses it: selected dependencies are tested mechanically.

## Meaning of the external arguments

The allowed inputs are **general theorems for arbitrary objects**: self-adjoint spectral theory, scalar Stieltjes theory, algebraicity/Puiseux, Perron/Frobenius, analytic implicit functions, normal forms, root factorization, integer-lattice and circle-group facts, and related finite-dimensional perturbation theory. See [EXTERNAL_ARGUMENTS.md](EXTERNAL_ARGUMENTS.md) for their precise interfaces.

The model-specific Dyson tree recursion, nondegeneracy, density classification, inverse estimates, and continuous physical branch selection are not bundled as external conclusions. Nevertheless, checking the *mathematical truth* of each general theorem parameter is a separate semantic task. `#print axioms` does not discharge theorem hypotheses. The two classical results explicitly cited in the manuscript remain cited external results rather than newly proven general theorems.

Random-matrix limits, universality, quantum ergodicity, and full spectral classifications from other cited papers belong to background literature. This project does not purport to formalize all cited papers, prove the generic external principles internally, or turn each displayed source formula into a separate Lean theorem. Its coverage concerns the formal manuscript results and their proof chains **relative to the declared external mathematical arguments**, with the above corrections and disclosed alternative steps.

## Mechanical audit of proof dependencies

[`ProofRouteAudit.lean`](ProofRouteAudit.lean) traverses project constants appearing in actual Lean-checked proof terms. For selected final results it checks that the intended tree Schur argument, shortest-path estimates, integral differentiation, Fourier/Doeblin contraction, manuscript-based Sym/NB nondegeneracy, M6 Poisson/`β` steps, M7 continuous-root selection, and the appendix Fourier/Taylor argument really appear in the dependency closure. It excludes specified superseded Möbius and degenerate-inverse endpoints. Running the verification script produces `validation/proof_routes.log`.

This audit addresses the concrete failure mode in which a useful intermediate lemma is stated but never used by the final theorem. It **does not** replace manual mathematical verification of the correspondence between the TeX and Lean theorem statements.
