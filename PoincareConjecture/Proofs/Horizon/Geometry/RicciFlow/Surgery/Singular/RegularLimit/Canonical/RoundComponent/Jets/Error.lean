import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem iteratedCovariantTensorDerivative_add (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) (m : ℕ) :
    D.iteratedCovariantTensorDerivative (fun x v => S x v + T x v) m =
      fun x v => D.iteratedCovariantTensorDerivative S m x v +
        D.iteratedCovariantTensorDerivative T m x v := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [LeviCivitaData.iteratedCovariantTensorDerivative, ih]
      exact D.covariantTensorDerivative_add
        (D.iteratedCovariantTensorDerivative_isSmooth hS m)
        (D.iteratedCovariantTensorDerivative_isSmooth hT m)

theorem tensorNorm_add_sq_le {k : ℕ} (S T : CovariantTensorEvaluation n M k) (x : M) :
    (g.tensorNorm (fun y v => S y v + T y v) x) ^ 2 ≤
      2 * (g.tensorNorm S x) ^ 2 + 2 * (g.tensorNorm T x) ^ 2 := by
  classical
  unfold RiemannianMetric.tensorNorm
  simp only [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  calc
    _ ≤ ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (2 * (S x (fun i => g.orthonormalBasis x (a i))) ^ 2 +
          2 * (T x (fun i => g.orthonormalBasis x (a i))) ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      nlinarith [sq_nonneg (S x (fun i => g.orthonormalBasis x (a i)) -
        T x (fun i => g.orthonormalBasis x (a i)))]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem sum_iterated_tensorNorm_add_sq_le (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) (m : ℕ) (x : M) :
    (∑ j ∈ Finset.range (m + 1),
      (g.tensorNorm (D.iteratedCovariantTensorDerivative (fun y v => S y v + T y v) j) x) ^ 2) ≤
      2 * (∑ j ∈ Finset.range (m + 1),
        (g.tensorNorm (D.iteratedCovariantTensorDerivative S j) x) ^ 2) +
      2 * (∑ j ∈ Finset.range (m + 1),
        (g.tensorNorm (D.iteratedCovariantTensorDerivative T j) x) ^ 2) := by
  simp_rw [iteratedCovariantTensorDerivative_add D hS hT]
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        (2 * (g.tensorNorm (D.iteratedCovariantTensorDerivative S j) x) ^ 2 +
          2 * (g.tensorNorm (D.iteratedCovariantTensorDerivative T j) x) ^ 2) :=
      Finset.sum_le_sum (fun j _ => tensorNorm_add_sq_le _ _ x)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

end PoincareConjecture.SingularRegularLimit.RoundComparison
