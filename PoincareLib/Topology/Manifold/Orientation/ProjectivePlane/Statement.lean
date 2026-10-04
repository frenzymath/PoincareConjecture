import PoincareLib.Topology.Manifold.ThreeDimensional.Orientation.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Certificate

/-!
# M83 orientation excludes a two-sided projective plane

The input is the existing signed smooth atlas. The conclusion excludes a
topological open product neighborhood, exactly as required by the global
surgery input. The embedding is not assumed smooth.

Source: Morgan--Tian Theorem 0.3, footnote 2, printed p. xii.
See `reviews/contracts/2026-09-17-m83-orientation-exclusion.md` and
`reviews/errata/2026-09-17-initial-projective-plane-producer.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- An oriented smooth three-manifold admits no topological open embedding
of the projective plane times an open interval. -/
def M83OrientationExclusionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M],
    OrientationCompatibleAtlas M → NoTrivialNormalProjectivePlane (M := M)

end PoincareMT
