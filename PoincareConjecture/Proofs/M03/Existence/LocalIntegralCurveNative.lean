import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_local_integralCurve
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 1
      (fun x : M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) x (V x)))
    (x₀ : M) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurveAt γ V 0 := by
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (t₀ := 0) (x₀ := x₀) (v := V) (hV x₀)

end PoincareConjecture
