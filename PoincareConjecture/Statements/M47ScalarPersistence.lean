import PoincareConjecture.Statements.Ch01.CurvatureCalculus
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

structure M47ScalarPersistencePredecessors : Prop where
  tensor_calculus :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  scalar_regular :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t

def M47LocalScalarPersistenceStatement : Prop :=
  ∀ K a : ℝ, 0 < K → 0 < a →
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ T : ℝ, 0 < T →
      ∀ (F : RicciFlow 3 M (Set.Icc 0 T)) (p : M),
        IsCompact (closure ((F.metric 0).ball p a)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p a,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p a,
          -1 ≤ (F.connection t).scalarCurvature x) →
        (∀ x ∈ (F.metric 0).ball p a,
          3 / 4 ≤ (F.connection 0).scalarCurvature x) →
        ∀ t ∈ Set.Icc 0 (min T tau), 1 / 4 ≤ (F.connection t).scalarCurvature p

end PoincareConjecture
