import PoincareLib.Geometry.Riemannian.Normalization.Definitions
import PoincareLib.Geometry.RicciFlow.Harnack.Basic

/-!
# Normalization and the shared metric interfaces

The reviewed completeness predicate and calibrated volume are the existing
library notions for the selected metric, including its extended distance
on a disconnected manifold. These bridges are definitional equalities.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
theorem normalizedMetricComplete_iff_metricComplete (g : RiemannianMetric 3 M) :
    normalizedMetricComplete g ↔ MetricComplete g := Iff.rfl

theorem NormalizedInitialMetric.metricComplete (data : NormalizedInitialMetric (M := M)) :
    MetricComplete data.metric := data.complete

theorem NormalizedInitialMetric.volume_eq_calibratedMetricVolume
    (data : NormalizedInitialMetric (M := M)) :
    data.volumeMeasure = calibratedMetricVolume data.metric :=
  data.volume_is_normalized_metric

end PoincareMT
