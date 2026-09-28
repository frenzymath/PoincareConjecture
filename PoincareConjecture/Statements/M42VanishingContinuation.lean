import PoincareConjecture.Definitions.M42VanishingContinuation












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedVanishingContinuationTheory : Prop where
  continuation : ∀ {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
    I.controlled_core = ∅ → Nonempty (RepairedVanishingContinuationData I branch)

end PoincareConjecture
