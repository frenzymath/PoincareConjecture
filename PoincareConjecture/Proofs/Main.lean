import PoincareConjecture.Statement
import PoincareLib.Topology.Manifold.Poincare

/-! The final assembly of the smooth and topological Poincare theorems. -/

set_option autoImplicit false

universe u

namespace PoincareConjecture

/-- A compact simply connected smooth three-manifold is diffeomorphic to the
standard three-sphere. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact PoincareMT.smoothPoincareSkeleton.{u}

/-- A compact simply connected topological three-manifold is homeomorphic to
the standard three-sphere. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  exact PoincareMT.topologicalPoincareSkeleton.{u}

end PoincareConjecture
