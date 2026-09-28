import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M13.OrdinaryFlow











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem scaleLeviCivitaData_scalarCurvature (D : LeviCivitaData g)
    [T2Space M] (Q : ℝ) (hQ : 0 < Q) (x : M) :
    (scaleLeviCivitaData D Q hQ).scalarCurvature x = D.scalarCurvature x / Q :=
  homothety_scalarCurvature_eq g (scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (identity_metricHomothety g Q hQ)
    D (scaleLeviCivitaData D Q hQ) x

end PoincareConjecture.M13

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem scaleMetric_normalized_pullback (N : EpsilonNeck g) (Q : ℝ) (hQ : 0 < Q) :
    (fun z v w => (Real.sqrt Q * N.scale)⁻¹ ^ 2 *
      roundCylinderPullback (M13.scaleSmoothMetric g Q hQ) N.coordinate_map z v w) =
    (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w) := by
  funext z v w
  simp only [roundCylinderPullback, M13.scaleSmoothMetric_inner, mul_inv_rev, mul_pow]
  field_simp [hQ.ne']
  rw [Real.sq_sqrt hQ.le]



noncomputable def scaleMetric [T2Space M] (N : EpsilonNeck g) (Q : ℝ) (hQ : 0 < Q) :
    EpsilonNeck (M13.scaleSmoothMetric g Q hQ) where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scale := Real.sqrt Q * N.scale
  scale_pos := mul_pos (Real.sqrt_pos.mpr hQ) N.scale_pos
  center := N.center
  connection := M13.scaleLeviCivitaData N.connection Q hQ
  scalar_center_pos := by
    rw [M13.scaleLeviCivitaData_scalarCurvature]
    exact div_pos N.scalar_center_pos hQ
  scale_eq_scalar := by
    rw [M13.scaleLeviCivitaData_scalarCurvature, N.scale_eq_scalar,
      Real.div_rpow N.scalar_center_pos.le hQ.le]
    have hpow : Q ^ (-1 / 2 : ℝ) = (Real.sqrt Q)⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hQ.le,
        ← Real.sqrt_eq_rpow]
    rw [hpow, div_inv_eq_mul, mul_comm]
  carrier := N.carrier
  carrier_open := N.carrier_open
  coordinate := N.coordinate
  coordinate_map := N.coordinate_map
  coordinate_map_eq := N.coordinate_map_eq
  coordinate_map_smooth := N.coordinate_map_smooth
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := N.coordinate_inverse_mem
  coordinate_inverse_left := N.coordinate_inverse_left
  coordinate_inverse_right := N.coordinate_inverse_right
  coordinate_inverse_smooth := N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := ⟨by
    rw [N.scaleMetric_normalized_pullback Q hQ]
    exact N.metric_comparison.close⟩

end PoincareConjecture.EpsilonNeck
