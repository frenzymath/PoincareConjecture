import PoincareConjecture.Proofs.M25.AppA_1_Necks.EuclideanCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff

namespace PoincareConjecture

theorem roundCylinderEuclideanModelCoefficients_symm
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelCoefficients x v w =
      roundCylinderEuclideanModelCoefficients x w v := by
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, roundCylinderModelCoefficients_apply]
  rw [real_inner_comm]
  congr 1
  exact mul_comm _ _

theorem roundCylinderEuclideanModelCoefficients_pos
    (x v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    0 < roundCylinderEuclideanModelCoefficients x v v := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have hw : T v ≠ 0 := by
    intro h
    exact hv (T.injective (h.trans T.map_zero.symm))
  change 0 < roundCylinderModelCoefficients (T x) (T v) (T v)
  rw [roundCylinderModelCoefficients_apply]
  have ha : 0 < 2 * (16 / (‖(T x).1‖ ^ 2 + 4) ^ 2) := by positivity
  by_cases hh : (T v).1 = 0
  · have ht : (T v).2 ≠ 0 := by
      intro ht
      exact hw (Prod.ext hh ht)
    simpa only [hh, inner_zero_left, mul_zero, zero_add] using mul_self_pos.mpr ht
  · exact add_pos_of_pos_of_nonneg
      (mul_pos ha (real_inner_self_pos.mpr hh)) (mul_self_nonneg _)

noncomputable def roundCylinderEuclideanModelMetric :
    RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients roundCylinderEuclideanModelCoefficients
    contDiff_roundCylinderEuclideanModelCoefficients
    roundCylinderEuclideanModelCoefficients_symm roundCylinderEuclideanModelCoefficients_pos

noncomputable def roundCylinderEuclideanModelConnection :
    LeviCivitaData roundCylinderEuclideanModelMetric :=
  roundCylinderEuclideanModelMetric.euclideanLeviCivitaData

end PoincareConjecture
