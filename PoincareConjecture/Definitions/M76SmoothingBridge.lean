import PoincareConjecture.Definitions.Ch18.SmoothingBridge

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M76SmoothingConclusion {M : Type u} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M)) : Prop :=
  Nonempty (SmoothingBridgeConclusion P)

end PoincareConjecture
