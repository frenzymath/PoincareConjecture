import PoincareLib.Topology.Manifold.ThreeDimensional.Orientation.PositiveCurvature
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Cover

/-!
# Projective-plane exclusion from a compact positive ancient slice

Synge orientability and M83 produce the source-carrier exclusion used in the
canonical-neighborhood alternatives from the curvature of the actual slice.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.AncientKappaSolution

/-- Strictly positive sectional curvature of one slice of a compact ancient
solution excludes a projective plane with a trivial topological normal bundle
on the solution carrier. -/
theorem noEmbeddedTrivialNormalProjectivePlane_of_compact_positive_sectional
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [CompactSpace M]
    (K : AncientKappaSolution 3 M) (t : ℝ)
    (hsec : (K.flow.connection t).StrictlyPositiveSectionalCurvature) :
    NoEmbeddedTrivialNormalProjectivePlane K :=
  (K.flow.metric t).noTrivialNormalProjectivePlane_of_compact_positive_sectional
    (K.flow.connection t) hsec

end PoincareMT.AncientKappaSolution
