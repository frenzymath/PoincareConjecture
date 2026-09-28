import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Statements.M44CapPersistence
import PoincareConjecture.Statements.M34StandardCapExistence
import PoincareConjecture.Statements.M35StandardCapUniqueness
import PoincareConjecture.Statements.M36MetricSurgery

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedControlledSchedulesTheory : Prop where
  schedules : RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    RepairedCapPersistenceTheory.{u} →
    ∀ epsilon_bound : ℝ, 0 < epsilon_bound →
      ∃ S : RepairedControlledSchedulesData.{u},
        2 * S.setup.epsilon ≤ epsilon_bound

end PoincareConjecture
