import PoincareConjecture.Statements.M21AsymptoticVolume
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Volume.BishopGromov








set_option autoImplicit false

open scoped Manifold ContMDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem m21Predecessors_from_M04 (n : ℕ) :
    AsymptoticVolumeRatioPredecessors.{u} n := by
  intro M _ _ _ g D
  exact D.curvatureTensorCalculus


















theorem asymptoticVolumeRatioBishopGromov (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n := by
  exact horizon_asymptoticVolumeRatioBishopGromov n P


theorem asymptoticVolumeRatioTheory (n : ℕ)
    (P : AsymptoticVolumeRatioPredecessors.{u} n) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n P


theorem m21AsymptoticVolumeRatioFromMilestones (n : ℕ) :
    AsymptoticVolumeRatioTheory.{u} n :=
  asymptoticVolumeRatioBishopGromov n (m21Predecessors_from_M04 n)

end PoincareConjecture
