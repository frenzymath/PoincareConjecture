import PoincareConjecture.Proofs.M04.CurvatureDerivativeCorrectionGeneral
import PoincareConjecture.Proofs.M04.CurvatureDerivativeHeatGeneral

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem curvatureDerivative_heat_inequality_interior_general
    (F : RicciFlow n M J) (m : ℕ) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    derivWithin
      (fun s ↦ ((F.connection s).curvatureDerivativeNorm m x) ^ 2) J t ≤
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
  apply curvatureDerivative_heat_inequality_interior_of_correction_general
    F m ht x
  simpa only [mul_assoc] using
    (inverse_metric_correction_le_general (g := F.metric t)
      (F.connection t) m x)

end PoincareConjecture.M04
