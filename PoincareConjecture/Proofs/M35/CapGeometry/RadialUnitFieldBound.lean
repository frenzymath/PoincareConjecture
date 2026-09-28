import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitField
import PoincareConjecture.Proofs.M35.CapGeometry.RadialPointIdentification
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)

include hrotation



theorem radialUnitField_connection_sq_le
    {x : StandardCapSpace} (hx : x ≠ 0) (w : StandardCapSpace) :
    g.inner x (D.connection (radialUnitField g) x w)
      (D.connection (radialUnitField g) x w) ≤
      (axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖) ^ 2 * g.inner x w w := by
  let U := radialUnitField g x
  let a := g.inner x U w
  have hunit : g.inner x U U = 1 := radialUnitField_unit g hrotation hx
  have hproj : g.inner x (w - a • U) (w - a • U) = g.inner x w w - a ^ 2 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      hunit, g.symm x w U]
    change g.inner x w w - a * a - a * (a - a * 1) = g.inner x w w - a ^ 2
    ring
  rw [radialUnitField_connection D hrotation hx]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change _ * (_ * g.inner x (w - a • U) (w - a • U)) ≤ _
  rw [hproj]
  nlinarith only [sq_nonneg
    ((axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖) * a)]



theorem radial_shape_le_inverse_tip_distance
    (P : M35StandardCapPredecessors) (hsec : D.NonnegativeSectionalCurvature)
    (hcomplete : MetricComplete g) {x : StandardCapSpace}
    (hd : 0 < (g.edist 0 x).toReal) :
    0 ≤ axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖ ∧
      axisWarpingSlope g ‖x‖ / axisWarpingRadius g ‖x‖ ≤ 1 / (g.edist 0 x).toReal := by
  have hx : x ≠ 0 := by
    intro hx
    have hzero : g.edist 0 x = 0 := by
      rw [hx]
      exact @edist_self StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace 0
    simp only [hzero, ENNReal.toReal_zero, lt_self_iff_false] at hd
  have hr := norm_pos_iff.mpr hx
  have hs : 0 < radialArclength g ‖x‖ := by
    simpa only [radialArclength_zero] using radialArclength_strictMono g hr
  have hdist : (g.edist 0 x).toReal ≤ radialArclength g ‖x‖ := by
    apply ENNReal.toReal_le_of_le_ofReal hs.le
    rw [(rotational_scalar_edist_eq_axis P D hrotation x).2]
    exact edist_axis_le_radialArclength g hr.le
  have hnonneg := axisWarpingSlope_nonneg D hrotation hsec hcomplete hr
  refine ⟨div_nonneg hnonneg (axisWarpingRadius_pos g hr).le, ?_⟩
  apply (div_le_div_iff₀ (axisWarpingRadius_pos g hr) hd).mpr
  calc
    axisWarpingSlope g ‖x‖ * (g.edist 0 x).toReal ≤
        axisWarpingSlope g ‖x‖ * radialArclength g ‖x‖ :=
      mul_le_mul_of_nonneg_left hdist hnonneg
    _ ≤ axisWarpingRadius g ‖x‖ := axisWarpingSlope_mul_arclength_le D hrotation hsec hr
    _ = 1 * axisWarpingRadius g ‖x‖ := (one_mul _).symm



theorem radial_shape_bound_on_ball
    (P : M35StandardCapPredecessors) (hsec : D.NonnegativeSectionalCurvature)
    (hcomplete : MetricComplete g) (x : StandardCapSpace) (R : ℝ)
    (hfar : R < (g.edist 0 x).toReal) {y : StandardCapSpace}
    (hy : y ∈ g.ball x R) :
    y ≠ 0 ∧ 0 ≤ axisWarpingSlope g ‖y‖ / axisWarpingRadius g ‖y‖ ∧
      axisWarpingSlope g ‖y‖ / axisWarpingRadius g ‖y‖ ≤
        1 / ((g.edist 0 x).toReal - R) := by
  have hxy : (g.edist x y).toReal < R := ENNReal.toReal_lt_of_lt_ofReal hy
  have htriangle := (abs_le.mp (g.abs_toReal_edist_sub_le 0 x y)).2
  have hypos : 0 < (g.edist 0 y).toReal := by linarith
  have hyne : y ≠ 0 := by
    intro hzero
    have hdistzero : g.edist 0 y = 0 := by
      rw [hzero]
      exact @edist_self StandardCapSpace g.toEMetricSpace.toPseudoEMetricSpace 0
    simp only [hdistzero, ENNReal.toReal_zero, lt_self_iff_false] at hypos
  obtain ⟨hnonneg, hbound⟩ :=
    radial_shape_le_inverse_tip_distance D hrotation P hsec hcomplete hypos
  refine ⟨hyne, hnonneg, hbound.trans ?_⟩
  exact one_div_le_one_div_of_le (sub_pos.mpr hfar) (by linarith)



theorem radialUnitField_connection_sq_le_on_ball
    (P : M35StandardCapPredecessors) (hsec : D.NonnegativeSectionalCurvature)
    (hcomplete : MetricComplete g) (x : StandardCapSpace) (R : ℝ)
    (hfar : R < (g.edist 0 x).toReal) {y : StandardCapSpace}
    (hy : y ∈ g.ball x R) (w : StandardCapSpace) :
    g.inner y (D.connection (radialUnitField g) y w)
      (D.connection (radialUnitField g) y w) ≤
      (1 / ((g.edist 0 x).toReal - R)) ^ 2 * g.inner y w w := by
  obtain ⟨hyne, hn, hb⟩ :=
    radial_shape_bound_on_ball D hrotation P hsec hcomplete x R hfar hy
  have hww : 0 ≤ g.inner y w w := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, le_refl]
    · exact (g.pos y w hw).le
  exact (radialUnitField_connection_sq_le D hrotation hyne w).trans
    (mul_le_mul_of_nonneg_right (sq_le_sq₀ hn (by positivity) |>.mpr hb) hww)

end PoincareConjecture.M35.Uniqueness
