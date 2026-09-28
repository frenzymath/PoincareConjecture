import PoincareConjecture.Proofs.M04.CurvatureDerivativeHeatEndpoint

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureDerivative_heat_inequality_general_on_Icc
    {T : ℝ} (F : RicciFlow n M (Icc 0 T)) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2)
        (Icc 0 T) t ≤
      (F.connection t).laplacian
        (fun y ↦ ((F.connection t).curvatureDerivativeNorm m y) ^ 2) x -
      2 * ((F.connection t).curvatureDerivativeNorm (m + 1) x) ^ 2 +
      2 * (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight m : ℝ) *
        (F.connection t).curvatureDerivativeNorm m x *
          (∑ i ∈ Finset.range (m + 1),
            (F.connection t).curvatureDerivativeNorm i x *
              (F.connection t).curvatureDerivativeNorm (m - i) x) +
      2 * ((m + 4 : ℕ) : ℝ) * (n : ℝ) ^ (m + 6) *
        (F.connection t).curvatureDerivativeNorm 0 x *
        ((F.connection t).curvatureDerivativeNorm m x) ^ 2 := by
  exact curvatureDerivative_heat_inequality_general F m
    ⟨ht.1.le, ht.2⟩ x

end PoincareConjecture.M04
