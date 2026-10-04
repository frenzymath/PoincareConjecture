import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.LocalFiniteness
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/CompleteBallVolume.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Finite actual volume of balls in complete connected manifolds

The standard model balls in Morgan-Tian Theorem 13.2, p. 333,
and Lemma 17.12, p. 410, have finite calibrated volume. The workspace's
complete-ball theorem retains the specified Riemannian metric exactly.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.SurgeryVolume

/-- Complete connected model balls have finite actual calibrated volume,
as used in MT Theorem 13.2, p. 333, and Lemma 17.12, p. 410. -/
theorem calibratedMetricVolume_ball_lt_top {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (r : ℝ) :
    calibratedMetricVolume g (g.ball p r) < ⊤ := by
  have hsub : g.ball p r ⊆ {q | g.edist p q ≤ ENNReal.ofReal r} :=
    fun q hq => (show g.edist p q < ENNReal.ofReal r from hq).le
  exact (measure_mono hsub).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact g
      (g.isCompact_closedBall_of_metricComplete hc p r))

end PoincareMT.SurgeryVolume
