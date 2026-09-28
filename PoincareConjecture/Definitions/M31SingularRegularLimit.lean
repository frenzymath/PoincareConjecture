import PoincareConjecture.Definitions.Ch11.SingularLimits












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]




abbrev RepairedSingularRegularLimitData
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions F T M) := SingularLimitConclusion H

end PoincareConjecture
