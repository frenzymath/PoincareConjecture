import PoincareLib.Geometry.RicciFlow.AncientKappa.Volume.BishopGromov
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Curvature.IntrinsicCalculus

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem m21Predecessors_from_M04 (n : ℕ) :
    AsymptoticVolumeRatioPredecessors.{u} n := by
  intro M _ _ _ g D
  exact D.curvatureTensorCalculus

theorem m21AsymptoticVolumeRatioFromMilestones (n : ℕ) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n (m21Predecessors_from_M04 n)

end PoincareMT
