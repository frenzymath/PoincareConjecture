import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem horizon_curvature_eq (D D' : LeviCivitaData g) (x : M)
    (v w z : TangentSpace (𝓡 n) x) :
    D.curvature x v w z = D'.curvature x v w z := by
  exact D.curvatureOnFields_eq_of_contMDiffAt D'
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) z)

theorem horizon_curvatureTensor_eq (D D' : LeviCivitaData g) (x : M)
    (v w z u : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w z u = D'.curvatureTensor x v w z u := by
  simp only [curvatureTensor, D.horizon_curvature_eq D']

theorem horizon_curvatureTensorNorm_eq (D D' : LeviCivitaData g) (x : M) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm x := by
  simp only [curvatureTensorNorm, D.horizon_curvatureTensor_eq D']

end PoincareConjecture.LeviCivitaData
