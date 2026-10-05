import PoincareLib.Geometry.Riemannian.Normalization.Definitions
import PoincareLib.Geometry.RicciFlow.Pinching.Conclusion

/-!
# Existence of normalized initial metrics

The statement packages a normalized metric, a compatible connection, the
calibrated Hausdorff volume, all-radius small-ball noncollapsing, completeness,
finite total volume, and the explicit time-zero Hamilton--Ivey bridge used by
the later pinching milestone.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

structure NormalizedInitialMetricConclusion where
  data : NormalizedInitialMetric (M := M)
  initial_pinching : HamiltonIveyPinchedAt data.connection 0

end PoincareMT
