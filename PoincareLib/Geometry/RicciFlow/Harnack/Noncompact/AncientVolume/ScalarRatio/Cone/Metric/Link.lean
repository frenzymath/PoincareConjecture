import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RayDistance

/-!
# The compact asymptotic unit link

Identify based rays whose rescaled distances tend to zero. The resulting
metric quotient is compact because its distance is bounded by the source
distance at unit time and actual based rays are pointwise compact.

Reference: Kleiner--Lott, Theorem 41.2, Case 2, p. 2677, and Appendix G,
p. 2852 (corrected 2013). Smoothness and the cone realization are later steps.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}

/-- The actual metric quotient of minimizing rays by zero asymptotic distance. -/
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

/-- The quotient projection is continuous from the original pointwise ray
topology; its proof uses the derived unit-time distance bound. -/
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

/-- The compact link distance is the limit of actual rescaled source-ray
distances, with the metric quotient and compactness already constructed. -/
theorem tendsto_dist_asymptoticLinkProjection (hcomparison : RayComparison p)
    (γ η : basedMinimizingRays p) :
    Tendsto (fun L : ℝ => dist (rayExtension γ L) (rayExtension η L) / L)
      atTop (𝓝 (dist (asymptoticLinkProjection hcomparison γ)
        (asymptoticLinkProjection hcomparison η))) := by
  rw [dist_asymptoticLinkProjection]
  exact tendsto_asymptoticRayDistance hcomparison γ η

end Poincare.AncientVolume.ScalarRatio
