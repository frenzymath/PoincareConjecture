import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Definitions.Ch03.CurvatureReaction
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Statements.Ch01.CurvatureCalculus









set_option autoImplicit false
open scoped Manifold ContDiff Bundle
universe u
namespace PoincareConjecture


structure RicciFlowCurvatureTheory : Prop where
  tensor_calculus :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  curvature_norm_zero :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M),
      D.curvatureDerivativeNorm 0 x = D.curvatureTensorNorm x
  scalar_regular :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  curvature_evolution :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v₁ v₂ v₃ v₄ : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x v₁ v₂ v₃ v₄)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![v₁, v₂, v₃, v₄] + (F.connection t).curvatureReaction x v₁ v₂ v₃ v₄) J t
  ricci_evolution :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).ricci x v w)
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
          (F.connection t).ricciReaction x v w) J t
  local_derivative_estimates :
    ∀ (n k : ℕ) (K α r : ℝ), 0 < K → 0 < α → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (M : Type u) [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
          [T2Space M] [SecondCountableTopology M],
        ∀ (T : ℝ), 0 < T → T ≤ α / K →
        ∀ (F : RicciFlow n M (Set.Icc 0 T)) (p : M),
          IsCompact (closure ((F.metric 0).ball p r)) →
          (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
            (F.connection t).curvatureTensorNorm x ≤ K) →
          ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
            (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ ((k : ℝ) / 2)
  initial_derivative_estimates :
    ∀ (n k l : ℕ) (K α r : ℝ), 0 < K → 0 < α → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (M : Type u) [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
          [T2Space M] [SecondCountableTopology M],
        ∀ (T : ℝ), 0 < T → T ≤ α / K →
        ∀ (F : RicciFlow n M (Set.Icc 0 T)) (p : M),
          IsCompact (closure ((F.metric 0).ball p r)) →
          (∀ t ∈ Set.Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
          (∀ j ≤ l, ∀ x : M, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
          ∀ t ∈ Set.Icc 0 T, (0 < t ∨ k ≤ l) →
          ∀ x ∈ (F.metric 0).ball p (r / 2),
            (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ (((k - l : ℕ) : ℝ) / 2)
  metric_comparison :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (J : Set ℝ) (F : RicciFlow n M J) (s t K : ℝ),
      s ∈ J → t ∈ J → s ≤ t → 0 ≤ K →
      (∀ τ ∈ Set.Icc s t, ∀ x : M, (F.connection τ).curvatureTensorNorm x ≤ K) →
      ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      Real.exp (-2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v ≤
          (F.metric t).inner x v v ∧
        (F.metric t).inner x v v ≤
          Real.exp (2 * (n : ℝ) * K * (t - s)) * (F.metric s).inner x v v
  sectional_preservation :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      ∀ (T : ℝ), 0 < T → ∀ F : RicciFlow 3 M (Set.Icc 0 T),
      (F.connection 0).NonnegativeSectionalCurvature →
      ∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeSectionalCurvature
  ricci_preservation :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      ∀ (T : ℝ), 0 < T → ∀ F : RicciFlow 3 M (Set.Icc 0 T),
      (F.connection 0).NonnegativeRicciCurvature →
      ∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeRicciCurvature
  scalar_zero_rigidity :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (T : ℝ), 0 < T → ∀ F : RicciFlow 3 M (Set.Icc 0 T),
      (∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeSectionalCurvature) →
      ∀ p : M, (F.connection T).scalarCurvature p = 0 →
      ∀ t ∈ Set.Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x = 0
  scalar_lower_bound :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [CompactSpace M] (a b : ℝ) (F : RicciFlow n M (Set.Ico a b)),
      a < b → 0 < n → ∀ r0 : ℝ, r0 < 0 →
      (∀ x : M, r0 ≤ (F.connection a).scalarCurvature x) →
      ∀ t ∈ Set.Ico a b, ∀ x : M,
        r0 / (1 - 2 * r0 * (t - a) / (n : ℝ)) ≤ (F.connection t).scalarCurvature x
  normalized_scalar_lower_bound :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [CompactSpace M] (a b : ℝ) (F : RicciFlow 3 M (Set.Ico a b)),
      0 ≤ a → a < b →
      (∀ x : M, -6 / (1 + 4 * a) ≤ (F.connection a).scalarCurvature x) →
      ∀ t ∈ Set.Ico a b, ∀ x : M,
        -6 / (1 + 4 * t) ≤ (F.connection t).scalarCurvature x

end PoincareConjecture
