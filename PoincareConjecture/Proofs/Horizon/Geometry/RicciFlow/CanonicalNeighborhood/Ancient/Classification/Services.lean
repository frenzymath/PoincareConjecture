import PoincareConjecture.Statements.M27Providers









set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure AncientKappaClassificationServices : Prop where
  normalization :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (p : M) (b : ℝ), b ≤ 0 →
        Nonempty (AncientKappaNormalization K p b)
  two_dimensional_classification :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 2 M), Nonempty (TwoDimensionalAncientRoundCertificate K)

theorem M26CanonicalNeighborhoodPredecessors.classificationServices
    (P : M26CanonicalNeighborhoodPredecessors.{u}) : AncientKappaClassificationServices.{u} :=
  ⟨P.normalization, P.two_dimensional_classification⟩

theorem M27KappaAlternativePredecessors.classificationServices
    (P : M27KappaAlternativePredecessors.{u}) : AncientKappaClassificationServices.{u} :=
  ⟨P.normalization, P.two_dimensional_classification⟩

end PoincareConjecture
