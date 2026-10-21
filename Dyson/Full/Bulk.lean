import Dyson.Full.BulkGraph
import Dyson.Full.BulkAlgebra
import Dyson.Full.BulkConnectivity
import Dyson.Full.BulkMarkov
import Dyson.Full.BulkKernel
import Dyson.Full.BulkTransfer
import Dyson.Full.BulkPerron
import Dyson.Full.BulkBoundary
import Dyson.Full.BulkOriginData
import Dyson.Full.BulkCompact
import Dyson.Full.BulkDistance
import Dyson.Full.BulkSubstochastic
import Dyson.Full.BulkQuantitative
import Dyson.Full.BulkPhysical
import Dyson.Full.BulkStrip
import Dyson.Full.BulkNBQuantitative
import Dyson.Full.BulkNBStrip
import Dyson.Full.BulkNBNonbip
import Dyson.Full.BulkRestricted
import Dyson.Full.BulkEuclidean
import Dyson.Full.BulkComplete
import Dyson.Full.BulkMarkovComplete

/-!
The concrete bulk graph and Perron-conjugation arguments.
All statements below concern actual finite graphs and group-valued phases.
-/

namespace NonSymmetricDyson.Full.Bulk
open Resonance Nonbacktracking

variable {V H : Type*} [Fintype V] [CommGroup H]

/-- The full non-backtracking resonance classification, with connectivity
derived from the assumptions on the base graph. -/
theorem nonbacktracking_resonance_iff (G : BaseGraph V)
    (hd : ∀ v, 3 ≤ BulkGraph.NB.degree G v)
    (hc : StronglyConnected G.Adj) (root : G.Edge) (phase : G.Edge → H) :
    CycleResonant G.CanFollow phase ↔
      ∃ omega : V → H, ∀ e, phase e = (omega (G.tail e))⁻¹ * omega (G.head e) := by
  have ht := BulkGraph.NB.hasThreeNeighbors_of_degree G hd
  exact BulkGraph.NB.resonance_iff_vertex_potentials G ht root
    (BulkConnectivity.NB.stronglyConnected G ht hc) phase

end NonSymmetricDyson.Full.Bulk
