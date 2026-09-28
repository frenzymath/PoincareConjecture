import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Normalization













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem uniformKappaCapDerivativeBounds
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < D ∧ ∀ t : ℝ, t ≤ 0 → ∀ x : M,
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
                2 * (K.flow.connection t).ricciNormSq x| ≤
              B * (K.flow.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨B, hB, hbound⟩ :=
    ScalarDerivatives.uniform_normalized_scalar_jets P.scalarDerivativeServices
  refine ⟨B + 1, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K
  refine ⟨B, hB.le, by linarith, ?_⟩
  intro t ht x
  obtain ⟨N⟩ := P.normalization M K x t ht
  obtain ⟨hgradient, hevolution⟩ := hbound N.target x N.normalized_scalar
  exact ⟨N.scalarGradientNorm_le hB.le hgradient,
    N.scalarEvolution_bound P.scalarDerivativeServices ht hevolution⟩




theorem uniformKappaCapDerivativeFields
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (t C : ℝ) (U : Set M),
          t ≤ 0 → D ≤ C →
          (∃ B : ℝ, B < C ∧ ∀ x ∈ U,
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
          (∃ B : ℝ, B < C ∧ ∀ x ∈ U,
            |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
                2 * (K.flow.connection t).ricciNormSq x| ≤
              B * (K.flow.connection t).scalarCurvature x ^ 2) := by
  obtain ⟨D, hD, hbound⟩ := uniformKappaCapDerivativeBounds P
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K t C U ht hDC
  obtain ⟨B, _, hBD, hB⟩ := hbound K
  exact ⟨⟨B, hBD.trans_le hDC, fun x _ ↦ (hB t ht x).1⟩,
    ⟨B, hBD.trans_le hDC, fun x _ ↦ (hB t ht x).2⟩⟩

end PoincareConjecture
