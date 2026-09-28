import PoincareConjecture.Definitions.M77Transport
import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure M78EndpointConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P)
    (T : M77TransportConclusion P S) where
  identification : M ≃ₜ ThreeSphere

end PoincareConjecture
