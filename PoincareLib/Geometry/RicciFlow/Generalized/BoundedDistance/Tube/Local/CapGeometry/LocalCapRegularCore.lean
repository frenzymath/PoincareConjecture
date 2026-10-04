import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.CoreClosure
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.CapGeometry.LocalCapBoundary
import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity

/-!
# Regularity of a cap core

The regular defining function at each boundary point rules out an isolated
boundary sheet: the closed core is the closure of its interior.

Reference: Morgan--Tian, Definition 9.72, pp. 230--231, and
Proposition A.21, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem frontier_core_eq_boundary_m28 : frontier C.core = C.boundary_sphere := by
  rw [frontier, C.closed_core_eq_closure_core.symm, C.isOpen_core_m28.interior_eq,
    C.boundary_eq_closed_core_diff_core_m28]

end PoincareMT.CapCertificate
