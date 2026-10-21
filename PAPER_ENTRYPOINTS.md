# Paper theorem entry points

Import the main results with:

```lean
import Dyson.Paper.Main
```

Use `import Dyson.Paper` to include the manuscript's auxiliary results. The namespace prefix `NonSymmetricDyson.Paper.` is omitted in the table. General mathematical results that have not been formalized internally appear as **explicit theorem parameters**. Inspect the complete theorem types or generate `validation/theorem_signatures.log` to see the exact assumptions.

| Manuscript | Principal Lean declarations |
|---|---|
| M1: existence, uniqueness, analyticity, probability measures, and the original support-radius bound | `FoundationsTree.tree_existence_and_uniqueness`; `FoundationsTree.measure_spec` |
| M2: singular sets, boundary values, measure decomposition, and common support | `BoundaryTree.singular_sets_and_boundary_values`; `BoundaryTree.component_measure_decomposition`; `BoundaryTree.common_regular_support` |
| M3: uniform modulus and imaginary-part comparisons on the full strip | `RegularityTree.boundedness_of_solution` |
| M4: restricted measures on compact intervals and two-point Hölder regularity | `RegularityTree.regularity_of_solution` |
| M5: edge/cusp density asymptotics in the original power-law form | `SingularitiesAsymptotics.edge_symmetric`; `SingularitiesAsymptotics.cusp_symmetric`; `SingularitiesAsymptotics.edge_nonbacktracking`; `SingularitiesAsymptotics.cusp_nonbacktracking` |
| M6: off-support, ordinary strict bulk, and exceptional strict bulk estimates | `Linear.off_support`; `Linear.symmetric_bulk`; `Linear.symmetric_exceptional_bulk`; `Linear.nonbacktracking_bulk`; `Linear.nonbacktracking_exceptional_bulk` |
| M6: edge and cusp estimates | `LinearEdge.edge_symmetric`; `LinearEdge.edge_nonbacktracking`; `LinearCusp.cusp_symmetric`; `LinearCusp.cusp_nonbacktracking`; actual directed-edge coordinates: `LinearNB.edge`, `LinearNB.cusp` |
| M7: stable regions and bipartite balance | `Nonlinear.main_theorem_seven_bulk`; `Nonlinear.main_theorem_seven_away`; `Nonlinear.main_theorem_seven_off_support`; `Nonlinear.main_theorem_seven_balance` |
| M7: continuous edge/cusp branches with any previously fixed positive anchor | `Nonlinear.main_theorem_seven_edge_prescribed_anchor`; `Nonlinear.main_theorem_seven_cusp_prescribed_anchor` |
| Appendix: cyclic-matrix counterexample and second-order expansion | `CyclicFourier.appendix_counterexample`; `CyclicFourier.singular_beta_taylor` |
| Introduction: signed Jacobi weights and the Green-function recursion | `WeightedNBTree.root_green`; `WeightedNBTree.forward_recursion`; `WeightedNBTree.canonical_eq` |

Additional development is organized in `PerronFrame` (unique normalized Perron pair throughout the strip), `PerronMarkov` and `PerronRestricted` (the Fourier/Doeblin argument), `Spectral` (normalized local spectral expansion), `CubicSource` (conditional general form), `CubicNormalized` (actual Sym/NB models), and `BulkGraph`, `BulkStability`, `BulkOrigin`.

For individual manuscript labels and file links, see [CORRESPONDENCE.md](CORRESPONDENCE.md). The constants in M7 may depend on the fixed anchor, and the bipartite-origin result permits shrinking the neighborhood. The source and clarified manuscript texts are in [`source/`](source/); see [FIDELITY_REVIEW.md](FIDELITY_REVIEW.md) for fidelity and proof-method qualifications.
