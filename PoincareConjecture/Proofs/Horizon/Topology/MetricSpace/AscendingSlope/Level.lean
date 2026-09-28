import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.AscendingSlope
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

open Set Metric

namespace Poincare

theorem exists_level_point_of_local_ascent
    {X : Type*} [MetricSpace X] {f : X → ℝ} {x : X} {T c t : ℝ}
    (hcompact : IsCompact (closedBall x T)) (hT : 0 < T) (hc : 0 ≤ c)
    (hf : Continuous f) (hstart : f x ≤ t) (htarget : t ≤ f x + c * T)
    (hascent : ∀ y ∈ ball x T, f y < t → ∀ s : ℝ, 0 < s →
      ∃ z, dist y z < s ∧ c * dist y z < f z - f y) :
    ∃ q, f q = t ∧ dist x q ≤ T := by
  let K := closedBall x T ∩ f ⁻¹' Iic t
  have hx : x ∈ K := ⟨mem_closedBall_self hT.le, hstart⟩
  have hK : IsCompact K := hcompact.inter_right (isClosed_Iic.preimage hf)
  have hpenalty : ContinuousOn (fun y => f y - c * dist x y) K :=
    (hf.sub (continuous_const.mul (continuous_const.dist continuous_id))).continuousOn
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hpenalty
  have hqle : dist x q ≤ T := by
    simpa only [mem_closedBall, dist_comm] using hq.1
  refine ⟨q, ?_, hqle⟩
  apply le_antisymm hq.2
  by_contra! hqt
  have hvalue : f x - c * dist x x ≤ f q - c * dist x q := hmax hx
  simp only [dist_self, mul_zero, sub_zero] at hvalue
  have hqsmall : dist x q < T := by
    by_contra hnot
    have heq : dist x q = T := le_antisymm hqle (le_of_not_gt hnot)
    rw [heq] at hvalue
    linarith only [hvalue, htarget, hqt]
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (isOpen_Iio.preimage hf) q hqt
  obtain ⟨z, hqz, hzasc⟩ := hascent q
    (by simpa only [mem_ball, dist_comm] using hqsmall) hqt
    (min (T - dist x q) ε) (lt_min (sub_pos.mpr hqsmall) hε)
  have hzlevel : f z < t := hεsub (by
    rw [mem_ball, dist_comm]
    exact hqz.trans_le (min_le_right _ _))
  have hzball : z ∈ closedBall x T := by
    rw [mem_closedBall, dist_comm]
    have hsmall := hqz.trans_le (min_le_left _ _)
    linarith [dist_triangle x q z]
  have hpen : f z - c * dist x z ≤ f q - c * dist x q := hmax ⟨hzball, hzlevel.le⟩
  have htri : dist x z - dist x q ≤ dist q z := by
    linarith only [dist_triangle x q z]
  have hmul := mul_le_mul_of_nonneg_left htri hc
  nlinarith only [hpen, hmul, hzasc]

theorem infDist_level_le_of_local_ascent
    {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x : X} {c t : ℝ}
    (hc : 0 < c) (hf : Continuous f) (ht : f x < t)
    (hascent : ∀ y ∈ ball x ((t - f x) / c), f y < t → ∀ s : ℝ, 0 < s →
      ∃ z, dist y z < s ∧ c * dist y z < f z - f y) :
    (f ⁻¹' {t}).Nonempty ∧ infDist x (f ⁻¹' {t}) ≤ (t - f x) / c := by
  obtain ⟨q, hq, hdist⟩ := exists_level_point_of_local_ascent
    (isCompact_closedBall x ((t - f x) / c)) (div_pos (sub_pos.mpr ht) hc)
    hc.le hf ht.le (by field_simp; linarith) hascent
  have hqmem : q ∈ f ⁻¹' {t} := hq
  exact ⟨⟨q, hqmem⟩, (infDist_le_dist_of_mem hqmem).trans hdist⟩

end Poincare
