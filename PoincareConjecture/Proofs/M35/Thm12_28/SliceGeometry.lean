import PoincareConjecture.Proofs.M35.Thm12_28.GeneralizedFlow
import PoincareConjecture.Statements.M35Providers









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem slice_homothety {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {t : ℝ} (ht : t ∈ J) :
    MetricHomothety (F.metric t) (metric F t) (sliceDiffeomorph ht).symm 1 := by
  intro x u v
  simpa only [one_mul] using metric_pullback F ht x u v



theorem slice_calculus (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J) :
    MetricHomothetyCalculus (F.metric t) (metric F t) (sliceDiffeomorph ht).symm 1 :=
  P.metric_homothety StandardCapSpace (slice J t).carrier _ _ _ 1 zero_lt_one
    (slice_homothety F ht)



theorem scalar_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (generalizedFlow F).scalar ⟨t, (sliceDiffeomorph ht).symm x⟩ =
      (F.connection t).scalarCurvature x := by
  exact (slice_calculus P F ht).scalar_eq (F.connection t) (connection F t) x |>.trans
    (div_one _)



theorem curvatureNorm_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    (generalizedFlow F).curvatureNorm ⟨t, (sliceDiffeomorph ht).symm x⟩ =
      (F.connection t).curvatureTensorNorm x := by
  exact (slice_calculus P F ht).curvature_norm_eq (F.connection t) (connection F t) x |>.trans
    (div_one _)



theorem complete_iff (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J) :
    MetricComplete ((generalizedFlow F).metric t) ↔ MetricComplete (F.metric t) :=
  (slice_calculus P F ht).complete_iff



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

end PoincareConjecture.M35.OrdinaryRealization
