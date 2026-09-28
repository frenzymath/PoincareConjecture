import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.LocalBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalFinite
















set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem volumeMeasure_ball_lt_top (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) (r : ℝ) :
    g.volumeMeasure (g.ball p r) < ⊤ := by
  apply (measure_mono (show g.ball p r ⊆ {q | g.edist p q ≤ ENNReal.ofReal r}
    from fun q hq => (show g.edist p q < ENNReal.ofReal r from hq).le)).trans_lt
  exact g.volumeMeasure_lt_top_of_isCompact (g.isCompact_closedBall_of_metricComplete hcomplete p r)

end PoincareConjecture.RiemannianMetric
