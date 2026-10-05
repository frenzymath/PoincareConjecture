import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Harnack
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.PointedCompactness
import PoincareLib.Topology.Manifold.NeckCap
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Blowup.DenseTime
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Proof

local notation "m29GeneralizedBoundedDistance" => PoincareMT.DenseTime.generalizedBoundedDistance


/-!
# Applied predecessors for M30

The checked supplier retains M29's actual universal operation. M30 owns the
geometric construction and selects its common threshold within its admission.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem m30ControlledBlowupPredecessorsFromMilestones :
    M30ControlledBlowupPredecessors.{u} := {
  m04 := ricciFlowCurvatureTheory
  m06 := differentialHarnackAncientTheory_from_M04
  m07 := fun H => pointedRicciFlowCompactness_from_M04 H
  m29 := m29GeneralizedBoundedDistance
    (m28BoundedDistance ⟨ricciFlowCurvatureTheory, m25NeckCapTopology⟩)
}

theorem m30ControlledGeneralizedBlowupLimitsFromMilestones :
    RepairedControlledBlowupLimitTheory.{u} :=
  m30ControlledGeneralizedBlowupLimits m30ControlledBlowupPredecessorsFromMilestones

end PoincareMT
