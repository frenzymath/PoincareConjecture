import PoincareConjecture.Definitions.Ch06.LGeometry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


structure LGeodesicTheory {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) [ConnectedSpace M] where

  minimizing_existence :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p₁ p₂ : M, ∃ p : BackwardTimePath F T τ₁ τ₂,
        p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂ ∧
          IsMinimizingBackwardLPath F T τ₁ τ₂ p

  euler_lagrange :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        IsMinimizingBackwardLPath F T τ₁ τ₂ p →
        IsBackwardLGeodesic F T τ₁ τ₂ p

  regularized_geodesic :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        IsBackwardLGeodesic F T τ₁ τ₂ p → Nonempty (RegularizedLGeodesicData p)

  first_variation :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        ∀ V : LVariation F T τ₁ τ₂ p,
          ∃ D : LVariationDerivativeData V,
            HasDerivAt (variationLLength V)
              (firstVariationBoundaryTerm V + firstVariationResidualIntegral V D) 0

  second_variation_jacobi :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        IsMinimizingBackwardLPath F T τ₁ τ₂ p →
        ∀ V : FixedEndpointLVariation F T τ₁ τ₂ p,
          ∃ D : LVariationDerivativeData V.toLVariation, ∃ q : ℝ,
            HasDerivAt (fun u ↦ deriv (variationLLength V.toLVariation) u) q 0 ∧
              q = secondVariationIndexForm V.toLVariation D ∧
              (q = 0 ↔ IsLJacobiField F T τ₁ τ₂ p (variationField V.toLVariation))

  extension_to_zero :
    ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        IsBackwardLGeodesic F T τ₁ τ₂ p →
        ∃ q : BackwardTimePath F T 0 τ₂,
          (∀ τ ∈ Set.Icc τ₁ τ₂, q.curve τ = p.curve τ) ∧
            IsBackwardLGeodesic F T 0 τ₂ q ∧
            (∀ q' : BackwardTimePath F T 0 τ₂,
              (∀ τ ∈ Set.Icc τ₁ τ₂, q'.curve τ = p.curve τ) →
              IsBackwardLGeodesic F T 0 τ₂ q' →
              ∀ τ ∈ Set.Icc 0 τ₂, q'.curve τ = q.curve τ)

  reduced_length_attained :
    ∀ τ : ℝ, 0 < τ → τ ≤ τmax → ∀ p q : M,
      ∃ path : BackwardTimePath F T 0 τ,
        path.curve 0 = p ∧ path.curve τ = q ∧
          IsMinimizingBackwardLPath F T 0 τ path ∧
          reducedLength F T p q τ =
            backwardLLength F T 0 τ path.curve / (2 * Real.sqrt τ)

  second_variation :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂,
        IsBackwardLGeodesic F T τ₁ τ₂ p →
        ∀ V : LVariation F T τ₁ τ₂ p,
          ∃ D : LVariationDerivativeData V, ∃ q : ℝ,
            HasDerivAt (fun u ↦ deriv (variationLLength V) u) q 0 ∧
              q = secondVariationBoundaryTerm V D + secondVariationIndexForm V D

  jacobi_initial_value :
    ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ < τ₂ → τ₂ ≤ τmax →
      ∀ p : BackwardTimePath F T τ₁ τ₂, ∀ R : RegularizedLGeodesicData p,
        ∀ Z : TangentSpace (𝓡 n) (p.curve τ₁),
          ∃ Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ),
            IsLJacobiField F T τ₁ τ₂ p Y ∧ HasLJacobiInitialDerivative R Y Z ∧
            (∀ Y' : ∀ τ, TangentSpace (𝓡 n) (p.curve τ),
              IsLJacobiField F T τ₁ τ₂ p Y' → HasLJacobiInitialDerivative R Y' Z →
              ∀ τ ∈ Set.Icc τ₁ τ₂, Y' τ = Y τ)

end PoincareConjecture
