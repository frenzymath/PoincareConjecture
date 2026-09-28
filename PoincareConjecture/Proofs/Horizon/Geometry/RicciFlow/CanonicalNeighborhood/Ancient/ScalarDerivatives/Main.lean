import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Normalization
import PoincareConjecture.Statements.M27Providers













set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem M27KappaAlternativePredecessors.scalarDerivativeServices
    (P : M27KappaAlternativePredecessors.{u}) : ScalarDerivativeServices.{u} where
  tensor_calculus := P.tensor_calculus
  scalar_evolution := P.scalar_evolution
  past_norm_le_scalar := P.past_norm_le_scalar
  normalization := P.normalization
  universal_noncollapsing := P.universal_noncollapsing
  normalized_compactness := P.normalized_compactness

theorem uniformKappaScalarDerivativeBounds_of_services
    (S : ScalarDerivativeServices.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ t, t ≤ 0 → ∀ x : M,
            0 < (K.flow.connection t).scalarCurvature x ∧
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            ∃ d : ℝ,
              HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
                d (Set.Iic 0) t ∧
              |d| ≤ B * (K.flow.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := ScalarDerivatives.uniform_normalized_scalar_jets S
  refine ⟨B + 1, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K
  refine ⟨B, hB.le, by linarith, ?_⟩
  intro t ht x
  obtain ⟨N⟩ := S.normalization M K x t ht
  obtain ⟨hgrad, htime⟩ := hbound N.target x N.normalized_scalar
  refine ⟨N.scale_eq ▸ N.scale_pos, N.scalarGradientNorm_le hB.le hgrad, ?_⟩
  exact N.scalarDerivWithin_bound S ht htime


theorem uniformKappaScalarDerivativeBounds
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ t, t ≤ 0 → ∀ x : M,
            0 < (K.flow.connection t).scalarCurvature x ∧
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            ∃ d : ℝ,
              HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
                d (Set.Iic 0) t ∧
              |d| ≤ B * (K.flow.connection t).scalarCurvature x ^ 2 :=
  uniformKappaScalarDerivativeBounds_of_services P.scalarDerivativeServices

theorem uniformKappaScalarDerivativeBounds_of_m26
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ t, t ≤ 0 → ∀ x : M,
            0 < (K.flow.connection t).scalarCurvature x ∧
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            ∃ d : ℝ,
              HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
                d (Set.Iic 0) t ∧
              |d| ≤ B * (K.flow.connection t).scalarCurvature x ^ 2 :=
  uniformKappaScalarDerivativeBounds_of_services P.scalarDerivativeServices

end PoincareConjecture
