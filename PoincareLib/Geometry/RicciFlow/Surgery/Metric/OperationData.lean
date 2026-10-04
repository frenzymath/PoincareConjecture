import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Local

/-!
Adapted from Mapher `PoincareMT/Definitions/M36MetricSurgery.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M36 repaired metric-surgery data

The operation retains the actual collapse map, inserted standard-cap chart,
metric/curvature controls, distance decrease, and finite-jet comparison.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedMetricSurgeryData (g₀ : StandardInitialMetric) where
  constants : MetricSurgeryConstants
  profile : SurgeryProfileLargeQ g₀ constants
  /-- Explicit proof-owned form of the source choice `C₀ \gg q`. -/
  profile_dominance : 100 * constants.q < constants.C₀
  operation : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M],
    ∀ {g : RiemannianMetric 3 M}
      (I : MetricSurgeryInput constants g),
        Nonempty (MetricSurgeryResult g₀ I)

end PoincareMT
