import PoincareConjecture.Definitions.M35StandardCapUniqueness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedStandardCapUniquenessTheory : Prop where
  estimates : ∀ g₀ : StandardInitialMetric,
    ∀ E : RepairedStandardCapExistenceData g₀,
      Nonempty (RepairedStandardCapUniquenessData g₀ E)

end PoincareConjecture
