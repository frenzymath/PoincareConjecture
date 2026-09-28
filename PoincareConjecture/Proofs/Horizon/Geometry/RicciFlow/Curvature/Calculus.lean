import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory













set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture



structure RicciFlowCurvatureCalculus : Prop where
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


theorem RicciFlowCurvatureTheory.toCalculus (hC : RicciFlowCurvatureTheory.{u}) :
    RicciFlowCurvatureCalculus.{u} where
  tensor_calculus := hC.tensor_calculus
  curvature_norm_zero := hC.curvature_norm_zero
  scalar_regular := hC.scalar_regular
  scalar_evolution := hC.scalar_evolution
  curvature_evolution := hC.curvature_evolution
  ricci_evolution := hC.ricci_evolution
  local_derivative_estimates := hC.local_derivative_estimates

instance : Coe RicciFlowCurvatureTheory.{u} RicciFlowCurvatureCalculus.{u} :=
  ⟨RicciFlowCurvatureTheory.toCalculus⟩

end PoincareConjecture
