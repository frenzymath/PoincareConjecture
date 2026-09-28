import PoincareConjecture.Definitions.M50FinitePrefix
import PoincareConjecture.Statements.M49VolumeLoss

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedFinitePrefixTheory : Prop where
  finite_prefix : ∀ F : SurgeryFlowData.{u},
    ∀ C : RepairedVolumeLossControls F,
      ∀ V : RepairedVolumeLossData F C,
        Nonempty (RepairedFinitePrefixData F C V)

end PoincareConjecture
