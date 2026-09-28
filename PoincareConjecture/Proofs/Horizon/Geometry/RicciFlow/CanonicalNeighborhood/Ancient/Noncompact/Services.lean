import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Services

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure NoncompactKappaServices : Prop extends ScalarDerivativeServices.{u} where
  two_dimensional_classification :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 2 M), Nonempty (TwoDimensionalAncientRoundCertificate K)

theorem M26CanonicalNeighborhoodPredecessors.noncompactServices
    (P : M26CanonicalNeighborhoodPredecessors.{u}) : NoncompactKappaServices.{u} where
  toScalarDerivativeServices := P.scalarDerivativeServices
  two_dimensional_classification := P.two_dimensional_classification

theorem M27KappaAlternativePredecessors.noncompactServices
    (P : M27KappaAlternativePredecessors.{u}) : NoncompactKappaServices.{u} where
  toScalarDerivativeServices := P.scalarDerivativeServices
  two_dimensional_classification := P.two_dimensional_classification

theorem NoncompactKappaServices.classificationServices
    (P : NoncompactKappaServices.{u}) : AncientKappaClassificationServices.{u} :=
  ⟨P.normalization, P.two_dimensional_classification⟩

end PoincareConjecture
