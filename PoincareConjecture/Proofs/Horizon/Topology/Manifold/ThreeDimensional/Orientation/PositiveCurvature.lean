import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Orientability
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Exclusion

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RiemannianMetric

theorem noTrivialNormalProjectivePlane_of_compact_positive_sectional
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hsec : D.StrictlyPositiveSectionalCurvature) :
    NoTrivialNormalProjectivePlane (M := M) := by
  obtain ⟨O⟩ := g.nonempty_orientationCompatibleAtlas_of_compact_positive_sectional D hsec
  exact m83OrientationExclusion M O

end PoincareConjecture.RiemannianMetric
