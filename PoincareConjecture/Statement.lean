import Mathlib

/-! The two endpoint propositions for the Poincare conjecture. -/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

/-- The unit three-sphere in four-dimensional real Euclidean space. -/
abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- Smooth Poincare, Morgan-Tian Corollary 0.2(a). -/
def SmoothPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M ThreeSphere ∞)

/-- Topological Poincare, without any smooth structure assumption. -/
def TopologicalPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₜ ThreeSphere)

end PoincareConjecture
