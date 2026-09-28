import PoincareConjecture.Definitions.Ch01.Topology
import PoincareConjecture.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

structure ClosedSimplyConnectedThreeManifoldConclusion where

  orientation : Nonempty (OrientationCompatibleAtlas M)

  cw_type : Topology.CWComplex (Set.univ : Set M)

  basepoint : M

  fundamental_group_subsingleton : Subsingleton (FundamentalGroup M basepoint)

  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)

  pi_three_integer :
    Nonempty (HomotopyGroup.Pi 3 M basepoint ≃* Multiplicative ℤ)

  homotopy_three_sphere : Nonempty (M ≃ₕ ThreeSphere)

end PoincareConjecture
