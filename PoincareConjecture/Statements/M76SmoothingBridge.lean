import PoincareConjecture.Definitions.M76SmoothingBridge















set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M76SmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (P : SmoothingBridgeInput (M := M)),
    M76SmoothingConclusion P

end PoincareConjecture
