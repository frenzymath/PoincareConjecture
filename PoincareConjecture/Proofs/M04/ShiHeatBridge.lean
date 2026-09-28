import PoincareConjecture.Proofs.M04.CurvatureDerivativeHeatEndpoint

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureDerivative_heat_inequality_on_Icc
    {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm 1 x) ^ 2)
        (Icc 0 T) t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm 1 y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm 2 x) ^ 2 +
      (196 * (n : ℝ) + 10 * (n : ℝ) ^ 7) *
        (F.connection t).curvatureDerivativeNorm 0 x *
          ((F.connection t).curvatureDerivativeNorm 1 x) ^ 2 := by
  exact curvatureDerivative_heat_inequality F ⟨ht.1.le, ht.2⟩ x

end PoincareConjecture.M04
