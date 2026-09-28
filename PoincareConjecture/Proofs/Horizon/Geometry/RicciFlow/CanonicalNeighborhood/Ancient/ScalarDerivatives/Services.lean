import PoincareConjecture.Statements.M26CanonicalNeighborhoods









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure ScalarDerivativeServices : Prop where
  tensor_calculus :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  scalar_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  past_norm_le_scalar :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
        (K.flow.connection t).curvatureTensorNorm x ≤
          (K.flow.connection b).scalarCurvature x
  normalization :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (p : M) (b : ℝ), b ≤ 0 →
        Nonempty (AncientKappaNormalization K p b)
  universal_noncollapsing :
    ∃ kappa₀ : ℝ, 0 < kappa₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K → AncientKappaNoncollapsed K.flow kappa₀
  normalized_compactness :
    ∀ N : NormalizedKappaCompactnessData,
      Nonempty (RedesignNormalizedKappaCompactnessConclusion N)

theorem M26CanonicalNeighborhoodPredecessors.scalarDerivativeServices
    (P : M26CanonicalNeighborhoodPredecessors.{u}) : ScalarDerivativeServices.{u} where
  tensor_calculus := P.tensor_calculus
  scalar_evolution := P.scalar_evolution
  past_norm_le_scalar := P.past_norm_le_scalar
  normalization := P.normalization
  universal_noncollapsing := P.universal_noncollapsing
  normalized_compactness := P.normalized_compactness

end PoincareConjecture
