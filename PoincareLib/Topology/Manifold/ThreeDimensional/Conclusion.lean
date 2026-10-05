import PoincareLib.Topology.Manifold.ThreeDimensional.Orientation.Basic
import PoincareLib.Topology.Homotopy.Sphere.ThreeSphere

/-!
# Topological and homotopy consequences for the initial three-manifold

The contract records the orientability, CW-type, low homotopy, and homotopy-
three-sphere consequences used later in the surgery and extinction path.  It
does not assume Poincare or any classification theorem.  The pinned Mathlib
version supplies the homotopy-group types but not the required duality,
Hurewicz, or manifold-to-CW arguments; those remain in the single milestone
proof obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- Complete outputs of the closed simply connected three-manifold topology step. -/
structure ClosedSimplyConnectedThreeManifoldConclusion where
  /-- The chosen atlas is globally orientable. -/
  orientation : Nonempty (OrientationCompatibleAtlas M)
  /-- A CW structure needed for the later Whitehead and Hurewicz arguments. -/
  cw_type : Topology.CWComplex (Set.univ : Set M)
  /-- A basepoint for based homotopy groups. -/
  basepoint : M
  /-- Simple connectedness expressed in the pinned fundamental-group API. -/
  fundamental_group_subsingleton : Subsingleton (FundamentalGroup M basepoint)
  /-- The second homotopy group vanishes. -/
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)
  /-- The third homotopy group is isomorphic to the integer group. -/
  pi_three_integer :
    Nonempty (HomotopyGroup.Pi 3 M basepoint ≃* Multiplicative ℤ)
  /-- The manifold is a homotopy three-sphere before the final homeomorphism step. -/
  homotopy_three_sphere : Nonempty (M ≃ₕ ThreeSphere)

end PoincareMT
