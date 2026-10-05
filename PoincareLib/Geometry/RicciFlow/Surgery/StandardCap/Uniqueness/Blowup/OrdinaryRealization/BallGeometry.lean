import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceGeometry

/-!
# Balls and volumes in the retained slices

Morgan-Tian, Theorem 12.28, pp. 323-324. The scale-one slice homothety
identifies the actual metric balls and their calibrated volumes used by
the Chapter 11 noncollapsing condition.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- The valid-slice identification maps each original metric ball onto the retained ball.
Used in Theorem 12.28, pp. 323-324. -/
theorem ball_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (p : StandardCapSpace) (r : ℝ) :
    (sliceDiffeomorph ht).symm '' (F.metric t).ball p r =
      ((generalizedFlow F).metric t).ball ((sliceDiffeomorph ht).symm p) r := by
  change _ = (metric F t).ball ((sliceDiffeomorph ht).symm p) r
  simpa only [Real.sqrt_one, one_mul] using (slice_calculus P F ht).ball_image p r

/-- The retained and original metric balls have exactly the same calibrated volume.
Used in Theorem 12.28, pp. 323-324. -/
theorem volume_ball (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (p : StandardCapSpace) (r : ℝ) :
    calibratedMetricVolume ((generalizedFlow F).metric t)
      (((generalizedFlow F).metric t).ball ((sliceDiffeomorph ht).symm p) r) =
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r) := by
  rw [← ball_image P F ht p r]
  exact volume_image P F ht _

end PoincareMT.M35.OrdinaryRealization
