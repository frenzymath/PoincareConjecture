import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.TensorLaplacianCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Variation.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.EuclideanNorm
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.TensorFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

end PoincareConjecture.TensorFiber

namespace PoincareConjecture.LeviCivitaData

open ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem horizon_curvatureDerivativeNorm_zero (D : LeviCivitaData g) (x : M) :
    D.curvatureDerivativeNorm 0 x = D.curvatureTensorNorm x := by
  classical
  have hsum {ι : Type} [Fintype ι] {k : ℕ} (f : (Fin (k + 1) → ι) → ℝ) :
      (∑ a : Fin (k + 1) → ι, f a) =
        ∑ i : ι, ∑ a : Fin k → ι, f (Fin.cons i a) := by
    simpa only [Fintype.sum_prod_type] using
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ι))
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
  unfold curvatureDerivativeNorm RiemannianMetric.tensorNorm
    iteratedCovariantTensorDerivative riemannEvaluation curvatureTensorNorm
  apply congrArg Real.sqrt
  simp_rw [hsum]
  simp only [Fintype.sum_unique]
  rfl

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

open ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

end PoincareConjecture.LeviCivitaData
