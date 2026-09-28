import PoincareConjecture.Definitions.M41NonemptyContinuation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedNonemptyContinuationTheory : Prop where
  continuation : ∀ {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
    I.controlled_core.Nonempty → Nonempty (RepairedNonemptyContinuationData I branch)

end PoincareConjecture
