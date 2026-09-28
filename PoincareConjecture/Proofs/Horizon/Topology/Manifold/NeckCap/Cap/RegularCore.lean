import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRegularCore
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
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

theorem frontier_core_eq_boundary : frontier C.core = C.boundary_sphere := by
  rw [frontier, C.closure_core_eq_closed_core, C.isOpen_core.interior_eq,
    C.boundary_eq_closed_core_diff_core]

end PoincareConjecture.CapCertificate
