import Dyson
open Lean Elab Command
namespace ProofRouteAudit

def isProject (n : Name) : Bool :=
  n.toString.startsWith "NonSymmetricDyson." || n.toString.startsWith "_private.Dyson."

partial def collect (env : Environment) (n : Name) : StateM NameSet Unit := do
  unless (← get).contains n do
    modify (·.insert n)
    let some ci := env.checked.get.find? n | return
    for dep in ci.getUsedConstantsAsSet.toList do
      if isProject dep then collect env dep

run_cmd do
  let env ← getEnv
  let cases : List (String × String × List String × List String) := [
    ("M1 actual tree", "NonSymmetricDyson.Paper.FoundationsTree.tree_existence_and_uniqueness",
      ["NonSymmetricDyson.Paper.TreeSolution.transform_equation",
       "NonSymmetricDyson.Paper.TreeSchur.weighted_branch_resolvent_identity"], []),
    ("Signed NB Jacobi Green recursion", "NonSymmetricDyson.Paper.WeightedNBTree.forward_recursion",
      ["NonSymmetricDyson.Paper.WeightedTreeSolution.transform_equation",
       "NonSymmetricDyson.Paper.WeightedTreeModel.jacobi_branch",
       "NonSymmetricDyson.Paper.TreeSchur.weighted_branch_resolvent_identity"], []),
    ("M3 shortest paths", "NonSymmetricDyson.Paper.RegularityTree.boundedness_of_solution",
      ["NonSymmetricDyson.Paper.FoundationsPaths.imaginary_parts_comparable"], []),
    ("M2 local isolation and compactness", "NonSymmetricDyson.Paper.BoundaryTree.singular_sets_and_boundary_values",
      ["NonSymmetricDyson.Paper.BoundaryLocalFinite.singular_finite_from_local_charts"], []),
    ("M2 support edge propagation", "NonSymmetricDyson.Paper.BoundaryTree.common_regular_support",
      ["NonSymmetricDyson.Paper.BoundaryPropagation.family_regularSupport_eq"], []),
    ("M4 actual Stieltjes derivative", "NonSymmetricDyson.Paper.RegularityTree.regularity_of_solution",
      ["NonSymmetricDyson.Paper.RegularityProofs.stieltjes_hasDerivAt"], []),
    ("Markov Fourier Doeblin", "NonSymmetricDyson.Paper.Perron.markov_second_singular_gap",
      ["NonSymmetricDyson.Paper.Perron.original_weighted_gap",
       "NonSymmetricDyson.Paper.Perron.doeblinAgainst_kernel_contraction"], []),
    ("M5 original Sym nondegeneracy", "NonSymmetricDyson.Paper.Singularities.regular_edge_symmetric",
      ["NonSymmetricDyson.Paper.SingularitiesNondegenerate.symmetric_positive"],
      ["NonSymmetricDyson.Full.Singularities.mobius_obstructs_local_solution_graph"]),
    ("M6 edge original Poisson beta", "NonSymmetricDyson.Paper.LinearEdge.edge_symmetric",
      ["NonSymmetricDyson.Paper.SingularityPoissonModel.edge_symmetric",
       "NonSymmetricDyson.Paper.LinearFrame.edge_inverse_from_frame"],
      ["NonSymmetricDyson.Full.MainLinearSingular.main_theorem_six_edge"]),
    ("M6 cusp original Poisson beta", "NonSymmetricDyson.Paper.LinearCusp.cusp_symmetric",
      ["NonSymmetricDyson.Paper.SingularityPoissonModel.cusp_symmetric",
       "NonSymmetricDyson.Paper.LinearFrame.inverse_from_frame",
       "NonSymmetricDyson.Paper.LinearGlobalization.upper_full_height_of_eventual"],
      ["NonSymmetricDyson.Full.MainLinearSingular.main_theorem_six_cusp"]),
    ("M6 actual NB edges", "NonSymmetricDyson.Paper.LinearNB.edge",
      ["NonSymmetricDyson.Paper.LinearEdge.edge_nonbacktracking"],
      ["NonSymmetricDyson.Full.MainLinearSingular.main_theorem_six_edge"]),
    ("M7 original NB data and physical branch", "NonSymmetricDyson.Paper.Nonlinear.main_theorem_seven_edge_prescribed_anchor",
      ["NonSymmetricDyson.Paper.SingularitiesFrontier.nb_frontier_data",
       "NonSymmetricDyson.Full.Nonlinear.continuous_root_disk_selection"],
      ["NonSymmetricDyson.Full.Singularities.mobius_obstructs_local_solution_graph"]),
    ("Appendix Fourier and algebraic remainder", "NonSymmetricDyson.Paper.CyclicFourier.appendix_counterexample",
      ["NonSymmetricDyson.Paper.CyclicFourier.canonical_inverse_order_fourier"], []),
    ("Appendix literal second order expansion", "NonSymmetricDyson.Paper.CyclicFourier.singular_beta_taylor",
      ["NonSymmetricDyson.Paper.CyclicFourier.relative_taylor_algebraic"], [])
  ]
  for (label, root, required, forbidden) in cases do
    let rootName := root.toName
    let some (.thmInfo _) := env.checked.get.find? rootName
      | throwError "Route root is not a checked theorem: {root}"
    let (_, deps) := (collect env rootName).run {}
    for name in required do
      unless deps.contains name.toName do
        throwError "Required proof dependency missing in {label}: {name}"
    for name in forbidden do
      if deps.contains name.toName then
        throwError "Excluded proof dependency appears in {label}: {name}"
    logInfo m!"ROUTE_PASS {label}: {root}"
  logInfo m!"PROOF_ROUTE_COUNT {cases.length}"
end ProofRouteAudit
