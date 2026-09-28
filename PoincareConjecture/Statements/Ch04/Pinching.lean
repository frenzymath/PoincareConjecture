import PoincareConjecture.Definitions.Ch04.Pinching
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

def HamiltonIveyPinchedAt {M : Type u}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (t : ℝ) : Prop :=
  0 ≤ t ∧
    (∀ x : M, -6 / (1 + 4 * t) ≤ D.scalarCurvature x) ∧
    (∀ x : M, 0 < D.negativeCurvaturePart x →
      D.scalarCurvature x ≥
        2 * D.negativeCurvaturePart x *
          (Real.log (D.negativeCurvaturePart x) + Real.log (1 + t) - 3))

def HamiltonIveyPinchedOn {M : Type u}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Set.Ico a b)) : Prop :=
  ∀ t ∈ Set.Ico a b, HamiltonIveyPinchedAt (F.connection t) t

structure HamiltonIveyPinchingConclusion {M : Type u}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (a b : ℝ)
    (F : RicciFlow 3 M (Set.Ico a b)) : Prop where
  persistence : HamiltonIveyPinchedOn F
  spectral_bridge :
    ∀ t ∈ Set.Ico a b, ∀ x : M, ∃ k1 k2 k3 : ℝ,
      k1 ≥ k2 ∧ k2 ≥ k3 ∧
      (F.connection t).leastSectionalCurvature x = k3 ∧
      (F.connection t).scalarCurvature x = 2 * (k1 + k2 + k3) ∧
      (F.connection t).curvatureTensorNorm x ^ 2 =
        4 * (k1 ^ 2 + k2 ^ 2 + k3 ^ 2)
  full_norm_bound :
    ∀ R₀ : ℝ, ∀ t ∈ Set.Ico a b, ∀ x : M,
      (F.connection t).scalarCurvature x ≤ R₀ →
      (F.connection t).curvatureTensorNorm x ≤
        13 * max R₀ (Real.exp 4)
  full_norm_bound_continuous :
    Continuous (fun R₀ : ℝ => 13 * max R₀ (Real.exp 4))

end PoincareConjecture
