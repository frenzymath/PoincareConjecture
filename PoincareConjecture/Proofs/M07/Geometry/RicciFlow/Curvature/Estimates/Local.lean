import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Theory

set_option autoImplicit false
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

abbrev LocalCurvatureDerivativeEstimates : Prop :=
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

end PoincareConjecture
