import PoincareConjecture.Definitions.M53SphereSeparation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedSphereSeparationTheory : Prop where
  separation :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M]
      [ConnectedSpace M],
      Nonempty (RepairedSphereSeparationData (M := M))

end PoincareConjecture
