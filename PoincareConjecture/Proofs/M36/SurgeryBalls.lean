import PoincareConjecture.Proofs.M36.GlobalMetricBounds
import PoincareConjecture.Proofs.M36.BallDistanceComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M36

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem sqrt_div_scalar_eq_scale (N : EpsilonNeck g) {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a / N.connection.scalarCurvature N.center) = Real.sqrt a * N.scale := by
  rw [← neck_scale_inverse_sq N, Real.sqrt_div ha, Real.sqrt_sq (inv_pos.mpr N.scale_pos).le,
    div_eq_mul_inv, inv_inv]

theorem surgeryMetric_radial_distance_bounds (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (hsmall : N.epsilon < 1 / 200) {C : ℝ} (hC : 0 ≤ C) (q : ℝ)
    {r : ℝ} (hr : 0 < r) (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :
    ENNReal.ofReal (Real.sqrt ((1 - 6 * N.epsilon) * Real.exp (-2 * C * N.epsilon)) *
        N.scale * radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖) ≤
      (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
        (neck_contraction_coefficient_pos N hsmall) hr).edist
          (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N)) y ∧
      (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
        (neck_contraction_coefficient_pos N hsmall) hr).edist
          (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N)) y ≤
      ENNReal.ofReal (Real.sqrt (1 + 6 * N.epsilon) *
        N.scale * radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖) := by
  let G := surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
    (neck_contraction_coefficient_pos N hsmall) hr
  have hbeta : 0 < (1 - 6 * N.epsilon) * Real.exp (-2 * C * N.epsilon) :=
    mul_pos (neck_contraction_coefficient_pos N hsmall) (Real.exp_pos _)
  have hupper : 0 < 1 + 6 * N.epsilon := by have := N.epsilon_pos; positivity
  constructor
  · have hbound := surgeryBall_radial_distance_lower g₀ (surgeryOuterRadius_pos g₀ N) G
      (div_pos hbeta N.scalar_center_pos) (fun z v => ?_) y
    · rw [sqrt_div_scalar_eq_scale N hbeta.le] at hbound
      exact hbound
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ N.scalar_center_pos).mpr
      have hb := (surgeryMetric_global_bounds g₀ N hcut hsmall hC q hr z v).1
      exact hb.trans_eq (mul_comm _ _)
  · have hbound := surgeryBall_radial_distance_upper g₀ (surgeryOuterRadius_pos g₀ N) G
      (div_pos hupper N.scalar_center_pos) (fun z v => ?_) y
    · rw [sqrt_div_scalar_eq_scale N hupper.le] at hbound
      exact hbound
    · rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ N.scalar_center_pos).mpr
      have hb := (surgeryMetric_global_bounds g₀ N hcut hsmall hC q hr z v).2
      exact (mul_comm _ _).trans_le hb

theorem surgeryMetric_cap_ball_bounds (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (hsmall : N.epsilon < 1 / 200) {C : ℝ} (hC : 0 ≤ C) (q : ℝ)
    {r : ℝ} (hr : 0 < r)
    (hsize : N.epsilon ≤ 1 / (surgeryCapRadius g₀ * (6 + 2 * C))) :
    (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
        (neck_contraction_coefficient_pos N hsmall) hr).ball
      (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N))
      (N.scale * (g₀.cylindrical_end.radius + 3)) ⊆
        surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
          g₀.metric.ball 0 (surgeryCapRadius g₀) ∧
      surgeryBallChart g₀ (surgeryOuterRadius g₀ N.epsilon) ''
          g₀.metric.ball 0 (surgeryCapRadius g₀) ⊆
        (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r N.scalar_center_pos
          (neck_contraction_coefficient_pos N hsmall) hr).ball
        (surgeryBallTip g₀ (surgeryOuterRadius_pos g₀ N))
        (N.scale * (g₀.cylindrical_end.radius + 5)) := by
  let A := surgeryCapRadius g₀
  let beta := (1 - 6 * N.epsilon) * Real.exp (-2 * C * N.epsilon)
  let R := fun y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) =>
    radialArclength g₀ ‖surgeryBallInclusion g₀ _ y‖
  have hA : 1 < A := by dsimp [A, surgeryCapRadius]; linarith [g₀.cylindrical_end.radius_pos]
  have hmargins := surgery_ball_factor_margins hA hC N.epsilon_pos.le
    (neck_contraction_coefficient_pos N hsmall) hsize
  change A - 1 < Real.sqrt beta * A ∧ Real.sqrt (1 + 6 * N.epsilon) * A < A + 1 at hmargins
  have hbeta : 0 < beta :=
    mul_pos (neck_contraction_coefficient_pos N hsmall) (Real.exp_pos _)
  have hupper : 0 < 1 + 6 * N.epsilon := by have := N.epsilon_pos; positivity
  have hinner : g₀.cylindrical_end.radius + 3 = A - 1 := by dsimp [A, surgeryCapRadius]; ring
  have houter : g₀.cylindrical_end.radius + 5 = A + 1 := by dsimp [A, surgeryCapRadius]; ring
  rw [surgeryBallChart_image_standardBall g₀ _ (surgeryCapRadius_pos g₀)
    (le_add_of_nonneg_right (inv_pos.mpr N.epsilon_pos).le), hinner, houter]
  constructor
  · intro y hy
    change R y < A
    have hlo := (surgeryMetric_radial_distance_bounds g₀ N hcut hsmall hC q hr y).1
    have hpos : 0 < N.scale * (A - 1) := mul_pos N.scale_pos (sub_pos.mpr hA)
    have hlt : Real.sqrt beta * N.scale * R y < N.scale * (A - 1) :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).mp (hlo.trans_lt hy)
    by_contra hnot
    have hge := le_of_not_gt hnot
    have hR := mul_le_mul_of_nonneg_left hge
      (mul_nonneg (Real.sqrt_nonneg beta) N.scale_pos.le)
    have hmargin := mul_lt_mul_of_pos_left hmargins.1 N.scale_pos
    nlinarith
  · intro y hy
    change R y < A at hy
    change _ < ENNReal.ofReal (N.scale * (A + 1))
    apply lt_of_le_of_lt (surgeryMetric_radial_distance_bounds g₀ N hcut hsmall hC q hr y).2
    apply ENNReal.ofReal_lt_ofReal_iff (mul_pos N.scale_pos (by linarith)) |>.mpr
    have hR := mul_lt_mul_of_pos_left hy
      (mul_pos (Real.sqrt_pos.mpr hupper) N.scale_pos)
    have hmargin := mul_lt_mul_of_pos_left hmargins.2 N.scale_pos
    nlinarith

end PoincareConjecture.M36
