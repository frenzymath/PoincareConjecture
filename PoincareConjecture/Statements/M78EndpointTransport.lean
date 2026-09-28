import PoincareConjecture.Definitions.M78EndpointTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M78EndpointTransportStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P)
    (T : M77TransportConclusion P S)
    (_hSmooth : SmoothPoincare.{u}),
    Nonempty (M78EndpointConclusion P S T)

end PoincareConjecture
