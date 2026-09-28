import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Definitions.Ch01.Normalization

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem normalizedMetricVolume_eq_smul_hausdorffVolume {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M]
    [BorelSpace M] [T3Space M] (g : RiemannianMetric 3 M) :
    normalizedMetricVolume g = euclideanHausdorffCalibration • g.hausdorffVolume :=
  rfl

end PoincareConjecture
