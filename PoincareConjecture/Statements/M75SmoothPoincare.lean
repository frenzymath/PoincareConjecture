import PoincareConjecture.Definitions.M75SmoothPoincare
import PoincareConjecture.Statement


















set_option autoImplicit false

universe u

open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture

def M75SmoothPoincareStatement : Prop :=
  ∀ (_hService : ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M],
    ∃ N : NormalizedInitialMetric (M := M),
      Nonempty (M75EndpointInput N)),
    SmoothPoincare.{u}

end PoincareConjecture
