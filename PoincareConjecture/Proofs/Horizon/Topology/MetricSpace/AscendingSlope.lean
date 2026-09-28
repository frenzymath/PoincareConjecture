import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace Poincare

theorem exists_sphere_point_of_local_ascent
    {X : Type*} [MetricSpace X] {f : X → ℝ} {x : X} {T c : ℝ}
    (hcompact : IsCompact (closedBall x T)) (hT : 0 < T) (hc : 0 ≤ c)
    (hf : ContinuousOn f (closedBall x T))
    (hascent : ∀ y ∈ ball x T, ∀ s : ℝ, 0 < s →
      ∃ z, dist y z < s ∧ c * dist y z < f z - f y) :
    ∃ q, dist x q = T ∧ c * T ≤ f q - f x := by
  have hx : x ∈ closedBall x T := mem_closedBall_self hT.le
  have hpenalty : ContinuousOn (fun y => f y - c * dist x y) (closedBall x T) :=
    hf.sub ((continuous_const.mul (continuous_const.dist continuous_id)).continuousOn)
  obtain ⟨q, hq, hmax⟩ := hcompact.exists_isMaxOn ⟨x, hx⟩ hpenalty
  have hqle : dist x q ≤ T := by simpa only [mem_closedBall, dist_comm] using hq
  have hboundary : dist x q = T := by
    apply le_antisymm hqle
    by_contra! hlt
    obtain ⟨z, hqz, hzasc⟩ := hascent q
      (by simpa only [mem_ball, dist_comm] using hlt) (T - dist x q) (sub_pos.mpr hlt)
    have hz : z ∈ closedBall x T := by
      rw [mem_closedBall, dist_comm]
      have htri := dist_triangle x q z
      linarith
    have hpen : f z - c * dist x z ≤ f q - c * dist x q := hmax hz
    have htri : dist x z - dist x q ≤ dist q z := by
      linarith only [dist_triangle x q z]
    have hmul := mul_le_mul_of_nonneg_left htri hc
    nlinarith only [hpen, hmul, hzasc]
  refine ⟨q, hboundary, ?_⟩
  have hvalue : f x - c * dist x x ≤ f q - c * dist x q := hmax hx
  simp only [dist_self, mul_zero, sub_zero, hboundary] at hvalue
  linarith only [hvalue]

theorem exists_small_excess_of_local_distance_ascent
    {X : Type*} [MetricSpace X] (p : X) {x : X} {T c : ℝ}
    (hcompact : IsCompact (closedBall x T)) (hT : 0 < T) (hc : 0 ≤ c)
    (hascent : ∀ y ∈ ball x T, ∀ s : ℝ, 0 < s →
      ∃ z, dist y z < s ∧ c * dist y z < dist p z - dist p y) :
    ∃ q, dist x q = T ∧ dist p x + dist x q - dist p q ≤ (1 - c) * T := by
  obtain ⟨q, hq, hvalue⟩ := exists_sphere_point_of_local_ascent
    (f := fun y => dist p y) hcompact hT hc
    (continuous_const.dist continuous_id).continuousOn hascent
  refine ⟨q, hq, ?_⟩
  rw [hq]
  nlinarith only [hvalue]

end Poincare
