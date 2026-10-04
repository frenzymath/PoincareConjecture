import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Pullback.Regularity
import PoincareLib.Geometry.Spacetime.Interval.RealTime

/-!
# Construction of moving-gauge metric geometry

The metric is the actual horizontal pullback. Its real-time regularity holds
within the full supplied interval, including its included endpoints.

Source: Morgan-Tian, Definitions 3.34-3.38, pp. 59-61.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

universe u v

namespace PoincareMT.MovingSpacetimeGauge

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

def pullbackMetric (e : MovingSpacetimeGauge F T C) (t : ℝ) : RiemannianMetric n C :=
  e.spatialMetric (T.realParam t)

theorem pullbackMetric_smooth (e : MovingSpacetimeGauge F T C) :
    RiemannianMetric.IsSmoothFamilyOn e.pullbackMetric K.domain := by
  have hp : ContMDiffOn (𝓘(ℝ).prod (𝓡 n)) (spacetimeModel n) ∞
      (fun p : ℝ × C => (T.realParam p.1, p.2)) (K.domain ×ˢ univ) :=
    (T.realParam_smoothOn.comp contMDiffOn_fst (fun _ hp => hp.1)).prodMk
      contMDiffOn_snd
  exact e.spatialMetricForm_joint_smooth.comp_contMDiffOn hp

/-- Every moving embedding carries its actual smooth horizontal pullback metric. -/
def geometry (e : MovingSpacetimeGauge F T C) : MovingSpacetimeGaugeGeometry e where
  metric := e.pullbackMetric
  smooth := e.pullbackMetric_smooth
  spatialTangentEquiv := e.spatialTangentEquiv
  spatialTangentEquiv_eq := e.spatialTangentEquiv_val
  metric_eq := by
    intro t x v w
    change (e.spatialMetric (T.realParam t)).inner x v w = _
    rw [T.realParam_coe]
    exact e.spatialMetric_inner t x v w

end

end PoincareMT.MovingSpacetimeGauge
