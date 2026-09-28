import PoincareConjecture.Definitions.Ch05.Compactness
import PoincareConjecture.Proofs.M07.Geometry.Manifold.ZeroDimensional

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem FlowCarrier.subsingleton_zero (C : FlowCarrier 0) : Subsingleton C.carrier := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 0)) C.carrier := C.chartedSpace
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  exact Poincare.subsingleton_of_preconnected_euclidean_zero C.carrier

end PoincareConjecture
