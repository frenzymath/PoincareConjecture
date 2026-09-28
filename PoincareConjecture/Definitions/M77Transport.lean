import PoincareConjecture.Definitions.Ch18.SmoothingBridge
import PoincareConjecture.Statements.Ch01.Topology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure M77TransportConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P) where

  model_simply_connected : @SimplyConnectedSpace S.model S.model_topology

  model_topology :
    Nonempty (@ClosedSimplyConnectedThreeManifoldConclusion S.model
      S.model_topology S.model_charted S.model_manifold)

end PoincareConjecture
