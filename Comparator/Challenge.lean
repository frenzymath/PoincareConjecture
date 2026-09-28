import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

def SmoothPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M ThreeSphere ∞)

def TopologicalPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₜ ThreeSphere)

namespace ComparatorTargets

theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  sorry

theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  sorry

end ComparatorTargets

end PoincareConjecture
