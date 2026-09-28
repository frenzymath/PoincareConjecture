import PoincareConjecture.Proofs.M45
import PoincareConjecture.Proofs.M45.Calibration
import PoincareConjecture.Proofs.M03
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M25
import PoincareConjecture.Proofs.M27.Providers
import PoincareConjecture.Proofs.M28
import PoincareConjecture.Proofs.M31
import PoincareConjecture.Proofs.M32.Providers
import PoincareConjecture.Proofs.M34
import PoincareConjecture.Proofs.M35.Providers
import PoincareConjecture.Proofs.M36
import PoincareConjecture.Proofs.M44
import PoincareConjecture.Proofs.M44.Providers

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

end PoincareConjecture
