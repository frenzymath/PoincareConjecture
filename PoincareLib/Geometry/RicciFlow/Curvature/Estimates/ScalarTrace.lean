import PoincareLib.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/ScalarEstimates.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Scalar minimum and trace estimates

Morgan-Tian, printed pp. 4-5 and Claim 4.2 on p. 64. The Hessian sign follows
by restricting to local integral curves and vanishing of the differential.
Its trace gives the Laplacian sign; the Ricci trace inequality is a
finite-dimensional calculation. Source and review records are task-local.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Filter Function Topology

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The intrinsic Hessian is nonnegative at a smooth local minimum. -/
theorem hessian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x)
    (v : TangentSpace (𝓡 n) x) : 0 ≤ D.hessian f x v v := by
  exact D.hessian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin v

/-- Tracing the local Hessian minimum inequality gives the Laplacian sign. -/
theorem laplacian_nonneg_of_isLocalMinAt (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (hmin : IsLocalMin f x) :
    0 ≤ D.laplacian f x := by
  exact D.laplacian_nonneg_of_isLocalMin_contMDiffAt
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hmin

/-- The squared scalar trace is at most the dimension times the Ricci squared norm. -/
theorem scalarCurvature_sq_le (D : LeviCivitaData g) (x : M) :
    (D.scalarCurvature x) ^ 2 ≤ (n : ℝ) * D.ricciNormSq x := by
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  have htrace := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i ↦ D.ricci x (b i) (b i))
  have hdiag : (∑ i, (D.ricci x (b i) (b i)) ^ 2) ≤
      ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2 := by
    exact Finset.sum_le_sum fun i _ ↦
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (D.ricci x (b i) (b j)))
        (Finset.mem_univ i)
  calc
    (D.scalarCurvature x) ^ 2 ≤ (n : ℝ) * ∑ i, (D.ricci x (b i) (b i)) ^ 2 := by
      simpa only [scalarCurvature, Finset.card_univ, Fintype.card_fin, hdim] using htrace
    _ ≤ (n : ℝ) * D.ricciNormSq x := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)

end PoincareMT.LeviCivitaData
