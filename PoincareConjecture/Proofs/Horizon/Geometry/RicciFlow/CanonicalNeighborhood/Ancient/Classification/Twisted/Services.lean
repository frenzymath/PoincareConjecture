import PoincareConjecture.Statements.M27Providers

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure AncientKappaCapServices : Prop where
  tensor_calculus :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  past_norm_le_scalar :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
        (K.flow.connection t).curvatureTensorNorm x ≤
          (K.flow.connection b).scalarCurvature x
  universal_noncollapsing :
    ∃ kappa₀ : ℝ, 0 < kappa₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K → AncientKappaNoncollapsed K.flow kappa₀

theorem M26CanonicalNeighborhoodPredecessors.capServices
    (P : M26CanonicalNeighborhoodPredecessors.{u}) : AncientKappaCapServices.{u} :=
  ⟨P.tensor_calculus 3, P.past_norm_le_scalar, P.universal_noncollapsing⟩

theorem M27KappaAlternativePredecessors.capServices
    (P : M27KappaAlternativePredecessors.{u}) : AncientKappaCapServices.{u} :=
  ⟨P.tensor_calculus 3, P.past_norm_le_scalar, P.universal_noncollapsing⟩

end PoincareConjecture
