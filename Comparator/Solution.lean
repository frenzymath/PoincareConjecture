import PoincareConjecture.Statement
import PoincareLib.Topology.Manifold.Poincare

/-! Elaborate the public statements in their Mathlib-only module before loading proof instances. -/

set_option autoImplicit false

universe u

namespace PoincareConjecture.ComparatorTargets

theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact PoincareMT.smoothPoincareSkeleton.{u}

theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  exact PoincareMT.topologicalPoincareSkeleton.{u}

end PoincareConjecture.ComparatorTargets
