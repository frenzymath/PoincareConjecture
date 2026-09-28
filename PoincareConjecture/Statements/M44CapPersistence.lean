import PoincareConjecture.Definitions.M44CapPersistence
import PoincareConjecture.Statements.M34StandardCapExistence
import PoincareConjecture.Statements.M35StandardCapUniqueness
import PoincareConjecture.Statements.M36MetricSurgery
import PoincareConjecture.Statements.M44Providers

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedCapPersistenceTheory : Prop where
  persistence : RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    ∀ g₀ : StandardInitialMetric,
      Nonempty (RepairedCapPersistenceData.{u} g₀)

end PoincareConjecture
