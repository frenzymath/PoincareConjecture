import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.CylinderPullback










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34




noncomputable def capCylindricalEnd {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (hn : capProfile a Real.pi = Real.sqrt 2) :
    StandardCylindricalEnd (capRiemannianMetric a ha hapi) where
  radius := a + 3 / 2
  radius_pos := by linarith
  closed_core := Metric.closedBall 0 (a + 3 / 2)
  closed_core_eq := (capRiemannianMetric_closedBall_zero ha hapi (by linarith)).symm
  core_compact := isCompact_closedBall _ _
  carrier := {x | a + 3 / 2 ≤ ‖x‖}
  carrier_eq := by
    rw [capRiemannianMetric_ball_zero ha hapi]
    ext x
    simp only [mem_ofPred_eq, mem_sdiff, mem_univ, Metric.mem_ball,
      dist_zero_right, true_and, not_lt]
  coordinate := capCylinderCoordinate (a + 3 / 2)
  inverse := capCylinderInverse (a + 3 / 2)
  coordinate_image := capCylinderCoordinate_image (by linarith)
  coordinate_left_inverse := by
    intro z hz
    apply capCylinderInverse_coordinate
    have hz0 : 0 ≤ z.2 := hz.2
    linarith
  coordinate_right_inverse := by
    intro x hx
    apply capCylinderCoordinate_inverse
    exact norm_pos_iff.mp (lt_of_lt_of_le (by linarith : 0 < a + 3 / 2) hx)
  inverse_domain := by
    intro x hx
    exact sub_nonneg.mpr hx
  collar := 1 / 2
  collar_pos := by norm_num
  coordinate_smooth := (capCylinderCoordinate_contMDiff (a + 3 / 2)).contMDiffOn
  inverse_smooth := by
    intro x hx
    apply (capCylinderInverse_contMDiffAt _ _).contMDiffWithinAt
    exact norm_pos_iff.mp (lt_of_lt_of_le (by linarith : 0 < a + 3 / 2) hx)
  metric_pullback := by
    intro z hz v w
    exact capRiemannianMetric_cylinder_pullback ha hapi hn _ z (by linarith) v w

end PoincareConjecture.M34
