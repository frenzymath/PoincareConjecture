import PoincareConjecture.Definitions.M41NonemptyContinuation
import PoincareConjecture.Definitions.M42VanishingContinuation









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedUnifiedContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (branch : RepairedBranchContinuationData I) where
  terminal : Sum (RepairedNonemptyContinuationData I branch)
    (RepairedVanishingContinuationData I branch)

end PoincareConjecture
