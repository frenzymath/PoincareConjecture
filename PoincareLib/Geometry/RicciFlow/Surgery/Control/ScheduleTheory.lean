import PoincareLib.Geometry.RicciFlow.Surgery.Control.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M45ControlledSchedules.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M45 calibrated setup and seed statement

The fixed setup and initial seeds precede the finite induction. The caller
may prescribe any positive bound on doubled epsilon before the setup is
chosen. M51 owns the global schedule, and continuation is a separate M48
obligation. Source: the initial parameter choices in Morgan--Tian Chapter 15,
pp. 354--355; epsilon is chosen before beta, C and the later selectors.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedControlledSchedulesTheory : Prop where
  schedules : RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    RepairedCapPersistenceTheory.{u} →
    ∀ epsilon_bound : ℝ, 0 < epsilon_bound →
      ∃ S : RepairedControlledSchedulesData.{u},
        2 * S.setup.epsilon ≤ epsilon_bound

end PoincareMT
