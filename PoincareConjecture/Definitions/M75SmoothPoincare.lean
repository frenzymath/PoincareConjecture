import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.M74ConnectedSumReduction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

structure M75EndpointInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] (N : NormalizedInitialMetric (M := M)) where
  global : RepairedGlobalFlowData N
  reduction : Nonempty (M74ReductionConclusion (global.certificate.flow.slice 0))

end PoincareConjecture
