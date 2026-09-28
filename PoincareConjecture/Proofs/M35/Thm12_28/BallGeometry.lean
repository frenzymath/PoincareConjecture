import PoincareConjecture.Proofs.M35.Thm12_28.SliceGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem ball_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (p : StandardCapSpace) (r : ℝ) :
    (sliceDiffeomorph ht).symm '' (F.metric t).ball p r =
      ((generalizedFlow F).metric t).ball ((sliceDiffeomorph ht).symm p) r := by
  change _ = (metric F t).ball ((sliceDiffeomorph ht).symm p) r
  simpa only [Real.sqrt_one, one_mul] using (slice_calculus P F ht).ball_image p r

theorem volume_ball (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (p : StandardCapSpace) (r : ℝ) :
    calibratedMetricVolume ((generalizedFlow F).metric t)
      (((generalizedFlow F).metric t).ball ((sliceDiffeomorph ht).symm p) r) =
        calibratedMetricVolume (F.metric t) ((F.metric t).ball p r) := by
  rw [← ball_image P F ht p r]
  exact volume_image P F ht _

end PoincareConjecture.M35.OrdinaryRealization
