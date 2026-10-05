import PoincareLib.Geometry.Riemannian.Comparison.Synge.Orientability
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Exclusion

/-!
# Positive sectional curvature excludes two-sided projective planes

The odd-dimensional Synge theorem supplies the actual signed atlas consumed by
M83. The proposed product neighborhood is only required to be topological.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.RiemannianMetric

/-- A compact connected positively curved smooth three-manifold contains no
projective plane with an open topological product neighborhood. -/
theorem noTrivialNormalProjectivePlane_of_compact_positive_sectional
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hsec : D.StrictlyPositiveSectionalCurvature) :
    NoTrivialNormalProjectivePlane (M := M) := by
  obtain ⟨O⟩ := g.nonempty_orientationCompatibleAtlas_of_compact_positive_sectional D hsec
  exact m83OrientationExclusion M O

end PoincareMT.RiemannianMetric
