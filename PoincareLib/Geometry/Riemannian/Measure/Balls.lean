import PoincareLib.Geometry.Riemannian.Comparison.Volume.LocalBall
import PoincareLib.Geometry.Riemannian.Distance.CompleteBalls
import PoincareLib.Geometry.Riemannian.Measure.LocalFinite

/-!
# Positive finite volumes of intrinsic balls

Local coordinate comparison gives positive volume to every positive-radius
ball. Completeness makes its volume finite, by compactness of closed balls.
These are the measure inputs to heat-kernel averaging and Gaussian moments.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Positive-radius intrinsic balls have positive retained volume. -/
theorem volumeMeasure_ball_pos (g : RiemannianMetric n M) (p : M)
    {R : ℝ} (hR : 0 < R) : 0 < g.volumeMeasure (g.ball p R) := by
  have hsmall := g.eventually_volumeMeasure_ball_bounds p (K := 2) (by norm_num)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, r < R :=
    nhdsWithin_le_nhds (Iio_mem_nhds hR)
  obtain ⟨r, hr, hrR, hbound⟩ :=
    (hpos.and (hlt.and hsmall)).exists
  have hvol : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) :=
    Metric.measure_ball_pos volume _ hr
  have hpos : 0 < g.volumeMeasure (g.ball p r) := by
    by_contra h
    have hz : g.volumeMeasure (g.ball p r) = 0 := le_antisymm (not_lt.mp h) zero_le
    simpa [hz] using hvol.trans_le hbound.2
  apply hpos.trans_le (measure_mono ?_)
  intro q hq
  exact (show g.edist p q < ENNReal.ofReal r from hq).trans_le
    (ENNReal.ofReal_le_ofReal hrR.le)

/-- Complete intrinsic balls of finite radius have finite retained volume. -/
theorem volumeMeasure_ball_lt_top (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) (r : ℝ) :
    g.volumeMeasure (g.ball p r) < ⊤ := by
  apply (measure_mono (show g.ball p r ⊆ {q | g.edist p q ≤ ENNReal.ofReal r}
    from fun q hq => (show g.edist p q < ENNReal.ofReal r from hq).le)).trans_lt
  exact g.volumeMeasure_lt_top_of_isCompact (g.isCompact_closedBall_of_metricComplete hcomplete p r)

end PoincareMT.RiemannianMetric
