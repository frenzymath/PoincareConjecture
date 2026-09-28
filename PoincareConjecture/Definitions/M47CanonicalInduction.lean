import PoincareConjecture.Definitions.Ch16.CanonicalInduction
import PoincareConjecture.Definitions.M46NoncollapseInduction










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedCanonicalInductionData
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) where
  induction : ∀ (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p),
    Nonempty (SurgeryCanonicalExtension.{u} p
      (Classical.choice (N.induction p hp)))

end PoincareConjecture
