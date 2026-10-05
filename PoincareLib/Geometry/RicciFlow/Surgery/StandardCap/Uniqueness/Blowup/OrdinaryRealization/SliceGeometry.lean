import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.GeneralizedFlow
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Predecessors

/-!
# Geometry of the actual ordinary slices

Morgan-Tian, Theorem 12.28, printed pp. 323-324. The supplied M13 metric
homothety calculus identifies the scalar, full curvature norm, selected
distance, and completeness of the Chapter 11 realization with the ordinary flow.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- The valid-slice identification is a metric homothety of scale one.
Used in Theorem 12.28, pp. 323-324. -/
theorem slice_homothety {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {t : ℝ} (ht : t ∈ J) :
    MetricHomothety (F.metric t) (metric F t) (sliceDiffeomorph ht).symm 1 := by
  intro x u v
  simpa only [one_mul] using metric_pullback F ht x u v

/-- Apply the earlier metric calculus to this precise slice identification.
Used in Theorem 12.28, pp. 323-324. -/
theorem slice_calculus (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J) :
    MetricHomothetyCalculus (F.metric t) (metric F t) (sliceDiffeomorph ht).symm 1 :=
  P.metric_homothety StandardCapSpace (slice J t).carrier _ _ _ 1 zero_lt_one
    (slice_homothety F ht)

/-- Scalar curvature in the generalized realization is that of the supplied ordinary flow.
Used in Theorem 12.28, pp. 323-324. -/
theorem scalar_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (generalizedFlow F).scalar ⟨t, (sliceDiffeomorph ht).symm x⟩ =
      (F.connection t).scalarCurvature x := by
  exact (slice_calculus P F ht).scalar_eq (F.connection t) (connection F t) x |>.trans
    (div_one _)

/-- The generalized curvature norm is the same full Hilbert-Schmidt norm as the ordinary one.
Used in Theorem 12.28, pp. 323-324. -/
theorem curvatureNorm_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (generalizedFlow F).curvatureNorm ⟨t, (sliceDiffeomorph ht).symm x⟩ =
      (F.connection t).curvatureTensorNorm x := by
  exact (slice_calculus P F ht).curvature_norm_eq (F.connection t) (connection F t) x |>.trans
    (div_one _)

/-- Completeness of a generalized slice is precisely completeness for the original metric.
Used in Theorem 12.28, pp. 323-324. -/
theorem complete_iff (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J) :
    MetricComplete ((generalizedFlow F).metric t) ↔ MetricComplete (F.metric t) :=
  (slice_calculus P F ht).complete_iff

/-- Slice distances use the original metric, not the ambient Euclidean distance.
Used in Theorem 12.28, pp. 323-324. -/
theorem edist_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x y : StandardCapSpace) :
    ((generalizedFlow F).metric t).edist
      ((sliceDiffeomorph ht).symm x) ((sliceDiffeomorph ht).symm y) =
        (F.metric t).edist x y := by
  change (metric F t).edist ((sliceDiffeomorph ht).symm x)
    ((sliceDiffeomorph ht).symm y) = (F.metric t).edist x y
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
    (slice_calculus P F ht).edist_eq x y

/-- Calibrated volume is preserved by the valid-slice identification.
Used in Theorem 12.28, pp. 323-324. -/
theorem volume_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (U : Set StandardCapSpace) :
    calibratedMetricVolume ((generalizedFlow F).metric t) ((sliceDiffeomorph ht).symm '' U) =
      calibratedMetricVolume (F.metric t) U := by
  change calibratedMetricVolume (metric F t) ((sliceDiffeomorph ht).symm '' U) = _
  have h := (slice_calculus P F ht).volume_image U
  exact h.trans ((congrArg (fun r : ℝ =>
    ENNReal.ofReal r * calibratedMetricVolume (F.metric t) U) (Real.one_rpow _)).trans
      (by rw [ENNReal.ofReal_one, one_mul]))

end PoincareMT.M35.OrdinaryRealization
