import PoincareLib.Geometry.RicciFlow.Harnack.Theorem
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem differentialHarnackAncientTheory_from_M04 : HarnackAncientTheory.{u} := by
  exact differentialHarnackAncientTheory ricciFlowCurvatureTheory

end PoincareMT
