import PoincareConjecture.Definitions.M43UnifiedContinuation
import PoincareConjecture.Statements.M41NonemptyContinuation
import PoincareConjecture.Statements.M42VanishingContinuation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedUnifiedContinuationTheory : Prop where
  continuation : RepairedNonemptyContinuationTheory.{u} →
    RepairedVanishingContinuationTheory.{u} →
    ∀ {F : SurgeryFlowData.{u}} {T : ℝ},
    ∀ (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
      Nonempty (RepairedUnifiedContinuationData I branch)

end PoincareConjecture
