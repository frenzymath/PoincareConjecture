import PoincareConjecture.Definitions.M47ComponentAnalytics
import PoincareConjecture.Statements.M47ScalarPersistence









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture


structure M47ComponentAnalyticPredecessors : Prop
    extends M47ScalarPersistencePredecessors.{u} where
  local_derivative_estimates :
    ∀ (k : ℕ) (K alpha r : ℝ), 0 < K → 0 < alpha → 0 < r →
      ∃ B : ℝ, 0 < B ∧
        ∀ (M : Type u) [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
          [T2Space M] [SecondCountableTopology M],
        ∀ T : ℝ, 0 < T → T ≤ alpha / K →
        ∀ (F : RicciFlow 3 M (Set.Icc 0 T)) (p : M),
          IsCompact (closure ((F.metric 0).ball p r)) →
          (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
            (F.connection t).curvatureTensorNorm x ≤ K) →
          ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
            (F.connection t).curvatureDerivativeNorm k x ≤ B / t ^ ((k : ℝ) / 2)
  metric_comparison :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (s t K : ℝ),
      s ∈ J → t ∈ J → s ≤ t → 0 ≤ K →
      (∀ tau ∈ Set.Icc s t, ∀ x : M, (F.connection tau).curvatureTensorNorm x ≤ K) →
      ∀ (x : M) (v : TangentSpace (𝓡 3) x),
      Real.exp (-2 * (3 : ℝ) * K * (t - s)) * (F.metric s).inner x v v ≤
          (F.metric t).inner x v v ∧
        (F.metric t).inner x v v ≤
          Real.exp (2 * (3 : ℝ) * K * (t - s)) * (F.metric s).inner x v v

end PoincareConjecture
