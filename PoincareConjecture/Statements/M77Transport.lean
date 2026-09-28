import PoincareConjecture.Definitions.M77Transport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M77TransportStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M]
    (P : SmoothingBridgeInput (M := M))
    (S : SmoothingBridgeConclusion P),
    Nonempty (M77TransportConclusion P S)

end PoincareConjecture
