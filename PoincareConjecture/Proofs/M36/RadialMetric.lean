import PoincareConjecture.Proofs.M36.RotationTransitivity

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace PoincareConjecture.M36

theorem axis_metric_formula_inner (g₀ : StandardInitialMetric) (r : ℝ)
    (v w : StandardCapSpace) :
    g₀.metric.inner (axisPoint r) v w =
      axisTangentialCoefficient g₀ r * inner ℝ v w +
        (axisRadialCoefficient g₀ r - axisTangentialCoefficient g₀ r) * v 0 * w 0 := by
  rw [axis_metric_formula]
  simp [PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply]
  ring

theorem standard_metric_radial_formula (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) (hx : x ≠ 0) (v w : StandardCapSpace) :
    g₀.metric.inner x v w =
      axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v w +
        (axisRadialCoefficient g₀ ‖x‖ - axisTangentialCoefficient g₀ ‖x‖) *
          inner ℝ (‖x‖⁻¹ • x) v * inner ℝ (‖x‖⁻¹ • x) w := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : StandardCapSpace := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hxnorm.ne']
  obtain ⟨L, hdet, hLu⟩ := exists_axis_isometry u hu
  have hLx : L (axisPoint ‖x‖) = x := by
    rw [axisPoint_eq_smul, map_smul, hLu]
    simp [u, smul_smul, hxnorm.ne']
  have hv : (L.symm v) 0 = inner ℝ u v := by
    rw [← hLu, L.inner_map_eq_flip]
    simp [axisBasis, EuclideanSpace.inner_single_left]
  have hw : (L.symm w) 0 = inner ℝ u w := by
    rw [← hLu, L.inner_map_eq_flip]
    simp [axisBasis, EuclideanSpace.inner_single_left]
  have hmetric := standardInitialMetric_isometry_inner g₀ L hdet
    (axisPoint ‖x‖) (L.symm v) (L.symm w)
  rw [hLx, L.apply_symm_apply, L.apply_symm_apply] at hmetric
  rw [hmetric, axis_metric_formula_inner, L.symm.inner_map_map, hv, hw]

end PoincareConjecture.M36
