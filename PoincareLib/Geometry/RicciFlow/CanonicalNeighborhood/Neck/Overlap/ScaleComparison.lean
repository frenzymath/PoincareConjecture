import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareLib.Geometry.Riemannian.Connection.Uniqueness

/-!
# Scale comparison from normalized scalar curvature

The frozen scalar normalization of each neck turns a lower scalar bound in
one neck into a comparison with the scale of a neck centered there.
Reference: Morgan--Tian, Proposition A.11(1), p. 503.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem scale_sq_mul_scalar_center :
    N.scale ^ 2 * N.connection.scalarCurvature N.center = 1 := by
  rw [N.scale_eq_scalar, ← Real.rpow_natCast, ← Real.rpow_mul N.scalar_center_pos.le]
  norm_num only [Nat.cast_ofNat, neg_div, neg_mul, one_div_mul_cancel, Real.rpow_neg_one]
  exact inv_mul_cancel₀ N.scalar_center_pos.ne'

theorem scale_sq_mul_scalar_center_of_connection (D : LeviCivitaData g) :
    N.scale ^ 2 * D.scalarCurvature N.center = 1 := by
  have hscalar : D.scalarCurvature N.center = N.connection.scalarCurvature N.center := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [D.curvatureTensor_eq N.connection N.center]
  rw [hscalar]
  exact N.scale_sq_mul_scalar_center

/-- Scalar curvature at a second neck's center controls its scale. -/
theorem scale_le_two_mul_of_normalized_scalar_ge (N' : EpsilonNeck g)
    (hscalar : (1 / 2 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature N'.center) :
    N'.scale ≤ 2 * N.scale := by
  have hnormal := N'.scale_sq_mul_scalar_center_of_connection N.connection
  have hmul := mul_le_mul_of_nonneg_left hscalar (sq_nonneg N'.scale)
  have hprod : N'.scale ^ 2 * (N.scale ^ 2 * N.connection.scalarCurvature N'.center) =
      N.scale ^ 2 := by
    calc
      _ = N.scale ^ 2 * (N'.scale ^ 2 * N.connection.scalarCurvature N'.center) := by ring
      _ = N.scale ^ 2 := by rw [hnormal, mul_one]
  rw [hprod] at hmul
  nlinarith [N.scale_pos, N'.scale_pos]

/-- A scalar error smaller than one half is sufficient for the coarse scale
comparison used by the sphere-containment argument. -/
theorem scale_le_two_mul_of_normalized_scalar_close (N' : EpsilonNeck g)
    (hscalar : |N.scale ^ 2 * N.connection.scalarCurvature N'.center - 1| < 1 / 2) :
    N'.scale ≤ 2 * N.scale :=
  N.scale_le_two_mul_of_normalized_scalar_ge N' (by linarith [(abs_lt.mp hscalar).1])

end PoincareMT.EpsilonNeck
