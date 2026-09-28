import PoincareConjecture.Proofs.Main

set_option autoImplicit false

universe u

namespace PoincareConjecture.ComparatorTargets

theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact PoincareConjecture.smoothPoincareSkeleton.{u}

theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  exact PoincareConjecture.topologicalPoincareSkeleton.{u}

end PoincareConjecture.ComparatorTargets
