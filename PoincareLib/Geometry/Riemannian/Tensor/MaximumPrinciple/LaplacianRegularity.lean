import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity
import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.HilbertFiber
import PoincareLib.Geometry.Riemannian.Tensor.TraceRegularity

/-!
# Rough Laplacians as smooth tensor fields

The rough Laplacian is the metric trace of two covariant derivatives. Smooth
covariant differentiation and smooth metric contraction therefore establish
its tensor regularity and give its pointwise Hilbert tensor fiber value.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The actual rough Laplacian of a smooth covariant tensor is smooth. -/
theorem tensorLaplacian_isSmooth (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.tensorLaplacian T) :=
  (D.covariantTensorDerivative_isSmooth (D.covariantTensorDerivative_isSmooth hT)).tensorTrace

/-- Pointwise multilinearity of the actual rough Laplacian. -/
theorem tensorLaplacian_multilinear (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) (p : M) :
    ∃ A : MultilinearMap ℝ (fun _ : Fin k => TangentSpace (𝓡 n) p) ℝ,
      ∀ v, D.tensorLaplacian T p v = A v :=
  (D.tensorLaplacian_isSmooth hT).1 p

/-- Bundle the geometric rough Laplacian in its Hilbert tensor fiber. -/
def tensorLaplacianFiber (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) (p : M) :
    TensorFiber (TangentSpace (𝓡 n) p) k :=
  TensorFiber.toMultilinear.symm (D.tensorLaplacian_multilinear hT p).choose

/-- The bundled rough Laplacian has exactly the retained geometric evaluation. -/
@[simp] theorem tensorLaplacianFiber_apply (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T) (p : M)
    (v : Fin k → TangentSpace (𝓡 n) p) :
    D.tensorLaplacianFiber hT p v = D.tensorLaplacian T p v :=
  ((D.tensorLaplacian_multilinear hT p).choose_spec v).symm

end PoincareMT.LeviCivitaData
