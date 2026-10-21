# Manuscript ↔ Lean correspondence

The source of record is [`source/main-article-1014.tex`](source/main-article-1014.tex). The formalization follows a clarified version of the manuscript, with scope and proof-method differences documented separately.

**Meaning of checked:** The Lean propositions compile under their *explicit general external mathematical hypotheses*, where those are present. This table does not claim that those hypotheses were all derived within the project. The table was condensed from the source release’s manuscript-to-Lean correspondence. The exact Lean proposition types, not these informal summaries, determine mathematical strength.

## Seven main theorem entry points

| Result | Topic | Lean declarations |
|---|---|---|
| M1 | Existence, uniqueness, analyticity, and measures | [`FoundationsTree.tree_existence_and_uniqueness`](Dyson/Paper/FoundationsTree.lean#L21), [`FoundationsTree.measure_spec`](Dyson/Paper/FoundationsTree.lean#L56) |
| M2 | Boundary values, measure decomposition and support | [`BoundaryTree.singular_sets_and_boundary_values`](Dyson/Paper/BoundaryTree.lean#L36), [`BoundaryTree.component_measure_decomposition`](Dyson/Paper/BoundaryTree.lean#L131) |
| M3 | Uniform bounds and comparison | [`RegularityTree.boundedness_of_solution`](Dyson/Paper/RegularityTree.lean#L17) |
| M4 | Hölder regularity and restricted measures | [`RegularityTree.regularity_of_solution`](Dyson/Paper/RegularityTree.lean#L45) |
| M5 | Regular edges and cusps (Sym/NB) | [`SingularitiesAsymptotics.edge_symmetric`](Dyson/Paper/SingularitiesAsymptotics.lean#L33), [`SingularitiesAsymptotics.cusp_nonbacktracking`](Dyson/Paper/SingularitiesAsymptotics.lean#L97) |
| M6 | Linear stability in bulk, edges, cusps | [`Linear.off_support`](Dyson/Paper/LinearRegular.lean#L16), [`LinearEdge.edge_symmetric`](Dyson/Paper/LinearEdge.lean#L12), [`LinearCusp.cusp_nonbacktracking`](Dyson/Paper/LinearCusp.lean#L106) |
| M7 | Nonlinear stability, balance and anchored branches | [`Nonlinear.main_theorem_seven_bulk`](Dyson/Paper/NonlinearStable.lean#L18), [`Nonlinear.main_theorem_seven_balance`](Dyson/Paper/NonlinearStable.lean#L52), [`Nonlinear.main_theorem_seven_edge_prescribed_anchor`](Dyson/Paper/NonlinearEndpoints.lean#L34) |

See the fuller original [`PAPER_ENTRYPOINTS.md`](PAPER_ENTRYPOINTS.md) for additional theorem variants and the Appendix.

## All 23 labeled results in the manuscript inventory

The manuscript line ranges come from the supplied source inventory. Each row points to representative Lean declarations; the table is not an assertion that the cited external theorem parameters have been discharged.

| Source label | Manuscript location | Description | Representative Lean source | Scope |
|---|---|---|---|---|
| `lem:cyclic-decomp` | [`755–788`](source/main-article-1014.tex#L755-L788) | Cyclic decomposition and eventual positivity | [`FoundationsPreliminaries.cyclic_decomposition`](Dyson/Paper/FoundationsPreliminaries.lean#L18); [`FoundationsPreliminaries.perron_frobenius`](Dyson/Paper/FoundationsPreliminaries.lean#L39) | Cited general input |
| `lem.PF` | [`791–804`](source/main-article-1014.tex#L791-L804) | Perron-Frobenius Theorem | [`FoundationsPreliminaries.cyclic_decomposition`](Dyson/Paper/FoundationsPreliminaries.lean#L18); [`FoundationsPreliminaries.perron_frobenius`](Dyson/Paper/FoundationsPreliminaries.lean#L39) | Cited general input |
| `thm:Existence and uniqueness` | [`819–837`](source/main-article-1014.tex#L819-L837) | Existence and uniqueness | [`FoundationsTree.tree_existence_and_uniqueness`](Dyson/Paper/FoundationsTree.lean#L21); [`FoundationsTree.row_bound`](Dyson/Paper/FoundationsTree.lean#L15) | Relative to external inputs |
| `thm.decompose of measure` | [`868–905`](source/main-article-1014.tex#L868-L905) | Decomposition of measures | [`BoundaryTree.singular_sets_and_boundary_values`](Dyson/Paper/BoundaryTree.lean#L36); [`Boundary.puiseux_expansion`](Dyson/Paper/Boundary.lean#L20) | Relative to external inputs |
| `thm.bound` | [`972–982`](source/main-article-1014.tex#L972-L982) | Boundedness of Solution | [`RegularityTree.boundedness_of_solution`](Dyson/Paper/RegularityTree.lean#L17); [`FoundationsPaths.walk_power_positive`](Dyson/Paper/FoundationsPaths.lean#L15) | Relative to external inputs |
| `thm.regularity` | [`988–1015`](source/main-article-1014.tex#L988-L1015) | Regularity of Solution | [`RegularityTree.regularity_of_solution`](Dyson/Paper/RegularityTree.lean#L45); [`Regularity.boundedness_of_solution`](Dyson/Paper/Regularity.lean#L17) | Relative to external inputs |
| `thm:singularities` | [`1064–1092`](source/main-article-1014.tex#L1064-L1092) | Singularity of Solution | [`SingularitiesAsymptotics.edge_symmetric`](Dyson/Paper/SingularitiesAsymptotics.lean#L33); [`Singularities.regular_edge_symmetric`](Dyson/Paper/Singularities.lean#L36) | Relative to external inputs |
| `thm.stability` | [`1103–1141`](source/main-article-1014.tex#L1103-L1141) | Stability of linear operator | [`Linear.off_support`](Dyson/Paper/LinearRegular.lean#L16); [`LinearBeta.coordinate_estimates`](Dyson/Paper/LinearBeta.lean#L11) | Relative to external inputs |
| `lem.stability2` | [`1199–1284`](source/main-article-1014.tex#L1199-L1284) | Stability of the solution | [`Nonlinear.main_theorem_seven_bulk`](Dyson/Paper/NonlinearStable.lean#L18); [`AnchorObstruction.physical_quadratic`](Dyson/Paper/AnchorObstruction.lean#L19) | Relative to external inputs |
| `lem:puiseux` | [`1292–1298`](source/main-article-1014.tex#L1292-L1298) | Proof of Proposition 4.2 in (cited literature) | [`BoundaryTree.puiseux_expansion`](Dyson/Paper/BoundaryTree.lean#L22); [`BoundaryTree.singular_sets_and_boundary_values`](Dyson/Paper/BoundaryTree.lean#L36) | Relative to external inputs |
| `lem:F-PF` | [`1703–1720`](source/main-article-1014.tex#L1703-L1720) | Supporting result | [`_private.Dyson.Paper.PerronFrame.0.NonSymmetricDyson.Paper.PerronFrame.real_eigenvector_multiple`](Dyson/Paper/PerronFrame.lean#L15); [`PerronFrame.normalized_pair_unique`](Dyson/Paper/PerronFrame.lean#L36) | Relative to external inputs |
| `lem:Q-second-singular-gap-lambda` | [`1784–1792`](source/main-article-1014.tex#L1784-L1792) | Supporting result | [`Perron.weightedSquare_add`](Dyson/Paper/PerronCombined.lean#L11); [`Perron.weightedNorm_pythagoras`](Dyson/Paper/PerronCombined.lean#L23) | Relative to external inputs |
| `pro.I-F-second` | [`2114–2120`](source/main-article-1014.tex#L2114-L2120) | Supporting result | [`Perron.original_uniform_saturated_restricted_inverse_bound`](Dyson/Paper/PerronRestricted.lean#L9); [`Perron.perron_inverse_transport`](Dyson/Paper/PerronTransport.lean#L12) | Relative to external inputs |
| `lem:B-bad-direction-nonsym-local` | [`2173–2235`](source/main-article-1014.tex#L2173-L2235) | Expansion around edge and cusp | [`Spectral.edge_cusp_spectral_expansion`](Dyson/Paper/Spectral.lean#L22); [`Spectral.coupling_block_bounds`](Dyson/Paper/SpectralBlockBounds.lean#L9) | Relative to external inputs |
| `prop:psi-positive-and-nondegenerate` | [`2668–2679`](source/main-article-1014.tex#L2668-L2679) | Supporting result | [`SingularitiesEqualityGraph.alternating_bipartition`](Dyson/Paper/SingularitiesEqualityGraph.lean#L10); [`SingularitiesEqualityGraph.nb_distance_two_constancy`](Dyson/Paper/SingularitiesEqualityGraph.lean#L22) | Relative to external inputs |
| `pro:Cubic equation` | [`3106–3142`](source/main-article-1014.tex#L3106-L3142) | Cubic equation | [`Cubic.equation_with_perron_data`](Dyson/Paper/Cubic.lean#L15); [`Cubic.equation_symmetric`](Dyson/Paper/Cubic.lean#L43) | Relative to external inputs |
| `pro.simple-bound-stability` | [`3195–3198`](source/main-article-1014.tex#L3195-L3198) | Simple bound for the stability operator | [`BulkStability.simple_bound`](Dyson/Paper/BulkStability.lean#L23); [`BulkStability.symmetric_bulk`](Dyson/Paper/BulkStability.lean#L60) | Relative to external inputs |
| `lem.zero-set-of-edge-defect` | [`3340–3357`](source/main-article-1014.tex#L3340-L3357) | Supporting result | [`BulkGraph.zero_set_of_edge_defect`](Dyson/Paper/BulkGraph.lean#L21); [`BulkGraph.minimizing_gauge`](Dyson/Paper/BulkGraph.lean#L26) | Relative to external inputs |
| `lem:UminusQ-graph-resonance` | [`3460–3476`](source/main-article-1014.tex#L3460-L3476) | Supporting result | [`BulkGraph.zero_set_of_edge_defect`](Dyson/Paper/BulkGraph.lean#L21); [`BulkGraph.minimizing_gauge`](Dyson/Paper/BulkGraph.lean#L26) | Relative to external inputs |
| `prop.bulk-stability-symmetric` | [`3834–3851`](source/main-article-1014.tex#L3834-L3851) | Bulk stability for symmetric matrices | [`BulkProofSteps.row_triangle`](Dyson/Paper/BulkProofSteps.lean#L14); [`BulkProofSteps.weighted_modulus_loss`](Dyson/Paper/BulkProofSteps.lean#L35) | Relative to external inputs |
| `lem.resonant-set-B` | [`4199–4216`](source/main-article-1014.tex#L4199-L4216) | Supporting result | [`BulkGraph.zero_set_of_edge_defect`](Dyson/Paper/BulkGraph.lean#L21); [`BulkGraph.minimizing_gauge`](Dyson/Paper/BulkGraph.lean#L26) | Relative to external inputs |
| `pro.bulk-stability-NB` | [`4275–4285`](source/main-article-1014.tex#L4275-L4285) | Bulk stability for non-backtracking matrix | [`BulkProofSteps.row_triangle`](Dyson/Paper/BulkProofSteps.lean#L14); [`BulkProofSteps.weighted_modulus_loss`](Dyson/Paper/BulkProofSteps.lean#L35) | Relative to external inputs |
| `prop.bipartite-origin-instability` | [`4583–4589`](source/main-article-1014.tex#L4583-L4589) | Bipartite instability at the origin | [`BulkOrigin.bad_vector_linear_opening`](Dyson/Paper/BulkOrigin.lean#L18); [`BulkOrigin.nearby_origin_inverse`](Dyson/Paper/BulkOrigin.lean#L28) | Relative to external inputs |

## How to read this mapping

1. Follow the source line range to understand the handwritten claim.
2. Open the linked `.lean` file and inspect the *entire declaration type*, including the parameters to the theorem.
3. Cross-reference [`EXTERNAL_ARGUMENTS.md`](EXTERNAL_ARGUMENTS.md) to determine which general principles have not been proved internally.
4. Consult [`FIDELITY_REVIEW.md`](FIDELITY_REVIEW.md) for the two statement clarifications, proof-route changes, and the role of the earlier expanded blueprint.
5. Generate `validation/theorem_signatures.log` using `python3 scripts/verify.py` to review full Lean types, or open the relevant `.lean` file directly.

This correspondence is a mathematical cross-reference adapted from the supplied project, not a machine-generated proof of theorem-statement equivalence between TeX and Lean.
