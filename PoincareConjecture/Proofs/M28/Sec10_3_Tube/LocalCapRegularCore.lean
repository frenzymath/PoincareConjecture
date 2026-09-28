import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.CoreClosure
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCapBoundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem frontier_core_eq_boundary_m28 : frontier C.core = C.boundary_sphere := by
  rw [frontier, C.closed_core_eq_closure_core.symm, C.isOpen_core_m28.interior_eq,
    C.boundary_eq_closed_core_diff_core_m28]

end PoincareConjecture.CapCertificate
