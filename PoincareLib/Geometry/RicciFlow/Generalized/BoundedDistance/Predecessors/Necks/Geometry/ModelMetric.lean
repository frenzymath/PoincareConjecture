import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.EuclideanCoefficients
import PoincareLib.Geometry.Riemannian.Metric.LocalExtension

/-!
# One fixed Euclidean metric for the cylinder comparison

The explicit cylinder coefficient field is smooth, symmetric and positive
everywhere. M07's Euclidean construction makes it an actual metric with
Levi-Civita data, fixed before all necks and error tolerances in
Morgan--Tian Lemma A.2, pp. 497-498. This construction does not assert its
curvature values; see the fixed-model-metric derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff

namespace PoincareMT

/-- Symmetry of the fixed cylinder coefficient field used in Lemma A.2. -/
theorem roundCylinderEuclideanModelCoefficients_symm
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelCoefficients x v w =
      roundCylinderEuclideanModelCoefficients x w v := by
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, roundCylinderModelCoefficients_apply]
  rw [real_inner_comm]
  congr 1
  exact mul_comm _ _

/-- Strict positivity of the fixed cylinder coefficient field at every
Euclidean point, as required for the metric in Lemma A.2. -/
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

/-- The fixed Euclidean cylinder metric for Lemma A.2, independent of
every neck, chart center and error tolerance. -/
noncomputable def roundCylinderEuclideanModelMetric :
    RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  RiemannianMetric.ofEuclideanCoefficients roundCylinderEuclideanModelCoefficients
    contDiff_roundCylinderEuclideanModelCoefficients
    roundCylinderEuclideanModelCoefficients_symm roundCylinderEuclideanModelCoefficients_pos

/-- The constructed Levi-Civita data for the fixed comparison metric in
Lemma A.2, pp. 497-498. -/
noncomputable def roundCylinderEuclideanModelConnection :
    LeviCivitaData roundCylinderEuclideanModelMetric :=
  roundCylinderEuclideanModelMetric.euclideanLeviCivitaData

end PoincareMT
