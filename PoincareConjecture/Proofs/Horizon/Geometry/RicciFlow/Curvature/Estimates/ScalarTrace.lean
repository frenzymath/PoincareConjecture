import PoincareConjecture.Proofs.M04.ScalarEstimates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.DerivativeTest






















set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Filter Function Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem hessian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.hessian f x v v := by
  exact D.hessian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin v


theorem laplacian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x) :
    0 ≤ D.laplacian f x := by
  exact D.laplacian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin

end PoincareConjecture.LeviCivitaData
