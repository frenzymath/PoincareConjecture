import PoincareConjecture.Proofs.M49.CalibratedVolume
import PoincareConjecture.Proofs.M09.RiemannianProper









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M49



theorem calibratedMetricVolume_ball_lt_top {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (r : ℝ) :
    calibratedMetricVolume g (g.ball p r) < ⊤ := by
  exact (measure_mono subset_closure).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact g
      (Proofs.M09.isCompact_closure_metric_ball g hc p r))

end PoincareConjecture.M49
