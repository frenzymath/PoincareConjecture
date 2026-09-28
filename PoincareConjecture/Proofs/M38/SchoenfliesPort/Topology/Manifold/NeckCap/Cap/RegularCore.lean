import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRegularCore
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity

open _root_.AddCircle
open _root_.PoincareConjecture
open _root_.PoincareConjecture.CapCertificate

namespace M38Schoenflies

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
  rw [frontier, C.closure_core_eq_closed_core, (CapCertificate.isOpen_core C).interior_eq,
    (CapCertificate.boundary_eq_closed_core_diff_core C)]

end PoincareConjecture.CapCertificate

end M38Schoenflies
