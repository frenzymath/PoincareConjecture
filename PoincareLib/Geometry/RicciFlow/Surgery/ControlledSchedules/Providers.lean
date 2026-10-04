import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.Calibration
import PoincareLib.Geometry.RicciFlow.Local.ExistenceUniquenessContinuation
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Topology.Manifold.NeckCap
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Kappa
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistance
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.RegularLimit
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Main
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Main
import PoincareLib.Geometry.RicciFlow.Surgery.CapPersistence.Providers

/-!
Supply M45's earlier services once, retaining the prescribed epsilon bound
used by M51/M52. The same selected Appendix A theory supplies M28 and M45.
These applications add no admission and do not prove M45's geometric outputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem m45ControlledSchedulesTheoryFromMilestones :
    RepairedControlledSchedulesTheory.{u} := by
  let A : RepairedNeckCapTopologyTheory.{u} := Classical.choice m25NeckCapTopology
  apply repairedControlledSchedules
    (fun M _ _ _ _ _ _ => ricciFlowLocalTheory (n := 3) (M := M))
    ricciFlowCurvatureTheory A m27KappaAlternativesFromMilestones
    (m28BoundedDistance ⟨ricciFlowCurvatureTheory, ⟨A⟩⟩)
    m31SingularRegularLimitTheory m32HornSelectionFromMilestones

theorem m45ControlledSchedulesBelowFromMilestones
    (epsilon_bound : ℝ) (hpositive : 0 < epsilon_bound) :
    ∃ S : RepairedControlledSchedulesData.{u},
      2 * S.setup.epsilon ≤ epsilon_bound :=
  m45ControlledSchedulesTheoryFromMilestones.schedules
    repairedStandardCapExistence m35StandardCapUniquenessFromMilestones
    repairedMetricSurgery m44CapPersistenceFromMilestones epsilon_bound hpositive

theorem m45ControlledSchedulesFromMilestones :
    Nonempty RepairedControlledSchedulesData.{u} := by
  obtain ⟨S, _⟩ := m45ControlledSchedulesBelowFromMilestones 1 zero_lt_one
  exact ⟨S⟩

end PoincareMT
