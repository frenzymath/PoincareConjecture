import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.PositiveCurvature
import PoincareConjecture.Definitions.M26CanonicalNeighborhoods








set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.AncientKappaSolution




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

end PoincareConjecture.AncientKappaSolution
