import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem scale_sq_mul_scalar_center_of_connection_m28 (D : LeviCivitaData g) :
    N.scale ^ 2 * D.scalarCurvature N.center = 1 := by
  have hscalar : D.scalarCurvature N.center = N.connection.scalarCurvature N.center := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [D.horizon_curvatureTensor_eq N.connection N.center]
  rw [hscalar]
  exact PoincareConjecture.M28.tube.neck_normalized_scalar_center N N.connection

theorem scale_le_two_mul_of_normalized_scalar_ge_m28 (N' : EpsilonNeck g)
    (hscalar : (1 / 2 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature N'.center) :
    N'.scale ≤ 2 * N.scale := by
  have hnormal := N'.scale_sq_mul_scalar_center_of_connection_m28 N.connection
  have hmul := mul_le_mul_of_nonneg_left hscalar (sq_nonneg N'.scale)
  have hprod : N'.scale ^ 2 * (N.scale ^ 2 * N.connection.scalarCurvature N'.center) =
      N.scale ^ 2 := by
    calc
      _ = N.scale ^ 2 * (N'.scale ^ 2 * N.connection.scalarCurvature N'.center) := by ring
      _ = N.scale ^ 2 := by rw [hnormal, mul_one]
  rw [hprod] at hmul
  nlinarith [N.scale_pos, N'.scale_pos]

theorem scale_le_two_mul_of_normalized_scalar_close_m28 (N' : EpsilonNeck g)
    (hscalar : |N.scale ^ 2 * N.connection.scalarCurvature N'.center - 1| < 1 / 2) :
    N'.scale ≤ 2 * N.scale :=
  N.scale_le_two_mul_of_normalized_scalar_ge_m28 N' (by linarith [(abs_lt.mp hscalar).1])

end PoincareConjecture.EpsilonNeck
