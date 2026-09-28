import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RayDistance











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}


def AsymptoticLink (p : X) (hcomparison : RayComparison p) :=
  @SeparationQuotient (basedMinimizingRays p)
    (asymptoticRayPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace

instance asymptoticLink_metricSpace (hcomparison : RayComparison p) :
    MetricSpace (AsymptoticLink p hcomparison) := by
  letI := asymptoticRayPseudoMetric hcomparison
  exact SeparationQuotient.instMetricSpace

def asymptoticLinkProjection (hcomparison : RayComparison p)
    (γ : basedMinimizingRays p) : AsymptoticLink p hcomparison :=
  @SeparationQuotient.mk (basedMinimizingRays p)
    (asymptoticRayPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace γ

theorem dist_asymptoticLinkProjection (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    dist (asymptoticLinkProjection hcomparison γ) (asymptoticLinkProjection hcomparison η) =
      asymptoticRayDistance γ η := by
  let := asymptoticRayPseudoMetric hcomparison
  exact SeparationQuotient.dist_mk γ η

theorem surjective_asymptoticLinkProjection (hcomparison : RayComparison p) :
    Function.Surjective (asymptoticLinkProjection hcomparison) := by
  exact @SeparationQuotient.surjective_mk (basedMinimizingRays p)
    (asymptoticRayPseudoMetric hcomparison).toUniformSpace.toTopologicalSpace



theorem continuous_asymptoticLinkProjection (hcomparison : RayComparison p) :
    Continuous (asymptoticLinkProjection hcomparison) := by
  apply continuous_iff_continuousAt.mpr
  intro γ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have heval : Continuous (fun η : basedMinimizingRays p => η.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  filter_upwards [heval.continuousAt.eventually (Metric.ball_mem_nhds (γ.1 1) hε)] with η hη
  rw [dist_asymptoticLinkProjection]
  exact (asymptoticRayDistance_le_dist_one hcomparison η γ).trans_lt hη

instance asymptoticLink_compactSpace [ProperSpace X] (hcomparison : RayComparison p) :
    CompactSpace (AsymptoticLink p hcomparison) :=
  (surjective_asymptoticLinkProjection hcomparison).compactSpace
    (continuous_asymptoticLinkProjection hcomparison)



theorem tendsto_dist_asymptoticLinkProjection (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    Tendsto (fun L : ℝ => dist (rayExtension γ L) (rayExtension η L) / L)
      atTop (𝓝 (dist (asymptoticLinkProjection hcomparison γ)
        (asymptoticLinkProjection hcomparison η))) := by
  rw [dist_asymptoticLinkProjection]
  exact tendsto_asymptoticRayDistance hcomparison γ η

end Poincare.AncientVolume.ScalarRatio
