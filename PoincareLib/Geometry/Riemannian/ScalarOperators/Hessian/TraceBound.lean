import PoincareLib.Geometry.Riemannian.ScalarOperators
import Mathlib.Algebra.Order.Chebyshev

/-! # The scalar Hessian trace inequality

The square of the metric trace is bounded by the dimension times the sum of
squares of all Hessian components in an orthonormal basis. This elementary
Cauchy--Schwarz estimate supplies the quadratic term in the Li--Yau argument.
-/

set_option autoImplicit false

open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Cauchy--Schwarz for the retained Hessian and its metric trace, including
dimension zero. No differentiability is needed for this algebraic bound. -/
theorem laplacian_sq_le_dim_mul_hessian_normSq (D : LeviCivitaData g)
    (f : M → ℝ) (x : M) :
    D.laplacian f x ^ 2 ≤ (n : ℝ) *
      ∑ i, ∑ j, D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  have hdiag : (∑ i, D.hessian f x (g.orthonormalBasis x i)
      (g.orthonormalBasis x i) ^ 2) ≤
      ∑ i, ∑ j, D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (D.hessian f x (g.orthonormalBasis x i)
        (g.orthonormalBasis x j))) (Finset.mem_univ i)
  calc
    D.laplacian f x ^ 2 ≤ (n : ℝ) *
        ∑ i, D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x i) ^ 2 := by
      simpa [laplacian, hdim] using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i =>
          D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x i)))
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)

end PoincareMT.LeviCivitaData
