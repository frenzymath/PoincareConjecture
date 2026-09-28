import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Algebra

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {k : ℕ}

lemma tensorLaplacian_const_mul (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T)) (c : ℝ) :
    D.tensorLaplacian (fun x v => c * T x v) =
      fun x v => c * D.tensorLaplacian T x v := by
  funext x v
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    D.covariantTensorDerivative_const_mul hT, D.covariantTensorDerivative_const_mul hDT,
    ← Finset.mul_sum]

lemma tensorLaplacian_add (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hDS : IsSmoothCovariantTensor (D.covariantTensorDerivative S))
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T)) :
    D.tensorLaplacian (fun x v => S x v + T x v) =
      fun x v => D.tensorLaplacian S x v + D.tensorLaplacian T x v := by
  funext x v
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    D.covariantTensorDerivative_add hS hT, D.covariantTensorDerivative_add hDS hDT,
    Finset.sum_add_distrib]

lemma tensorLaplacian_sub (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hDS : IsSmoothCovariantTensor (D.covariantTensorDerivative S))
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T)) :
    D.tensorLaplacian (fun x v => S x v - T x v) =
      fun x v => D.tensorLaplacian S x v - D.tensorLaplacian T x v := by
  funext x v
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    D.covariantTensorDerivative_sub hS hT, D.covariantTensorDerivative_sub hDS hDT,
    Finset.sum_sub_distrib]

end PoincareConjecture.LeviCivitaData
