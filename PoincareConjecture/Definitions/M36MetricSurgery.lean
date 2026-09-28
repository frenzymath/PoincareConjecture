import PoincareConjecture.Definitions.Ch13.MetricSurgery








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedMetricSurgeryData (g₀ : StandardInitialMetric) where
  constants : MetricSurgeryConstants
  profile : SurgeryProfileLargeQ g₀ constants

  profile_dominance : 100 * constants.q < constants.C₀
  operation : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M],
    ∀ {g : RiemannianMetric 3 M}
      (I : MetricSurgeryInput constants g),
        Nonempty (MetricSurgeryResult g₀ I)

end PoincareConjecture
