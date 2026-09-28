import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceNeck
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)

theorem strongNeckSource_preconnected : PreconnectedSpace (strongNeckOpen S) := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  let : PreconnectedSpace (Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  exact S.coordinate.surjective.denseRange.preconnectedSpace S.coordinate.continuous

variable (H : RescaledRawCylinderData (C := F.slice t)
  (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
  (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

@[instance_reducible] noncomputable def GeneralizedStrongNeck.rescaled_source_metricSpace :
    MetricSpace (strongNeckOpen S) := by
  let g := H.rescaling.flow.metric 0
  let : PreconnectedSpace (strongNeckOpen S) := strongNeckSource_preconnected S
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : strongNeckOpen S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : strongNeckOpen S → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (strongNeckOpen S) :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (strongNeckOpen S)
  exact EMetricSpace.toMetricSpace (fun x y => g.edist_ne_top x y)

theorem GeneralizedStrongNeck.rescaled_source_metricSpace_topology :
    let d := GeneralizedStrongNeck.rescaled_source_metricSpace S H
    (inferInstance : TopologicalSpace (strongNeckOpen S)) =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := rfl

theorem GeneralizedStrongNeck.rescaled_source_metricSpace_edist
    (x y : strongNeckOpen S) :
    letI := GeneralizedStrongNeck.rescaled_source_metricSpace S H
    edist x y = (H.rescaling.flow.metric 0).edist x y := rfl

end PoincareConjecture.M28
