import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace PoincareConjecture.M60

theorem exists_heinz_disk {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {u : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hnonneg : ∀ x ∈ Metric.closedBall 0 R, 0 ≤ u x) (hzero : 0 < u 0) :
    ∃ (p : E) (s : ℝ), 0 < s ∧ s ≤ R / 2 ∧ 0 < u p ∧
      Metric.closedBall p s ⊆ Metric.ball 0 R ∧
      R ^ 2 * u 0 ≤ 4 * s ^ 2 * u p ∧
      ∀ x ∈ Metric.closedBall p s, u x ≤ 4 * u p := by
  let F : E → ℝ := fun x => (R - ‖x‖) ^ 2 * u x
  have h0 : (0 : E) ∈ Metric.closedBall 0 R := Metric.mem_closedBall_self hR.le
  have hF : ContinuousOn F (Metric.closedBall 0 R) :=
    ((continuousOn_const.sub continuous_norm.continuousOn).pow 2).mul hu
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : E) R).exists_isMaxOn ⟨0, h0⟩ hF
  have hpR : ‖p‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  have hFp : R ^ 2 * u 0 ≤ (R - ‖p‖) ^ 2 * u p := by
    simpa only [F, norm_zero, sub_zero] using (show F 0 ≤ F p from hmax h0)
  have hFpos : 0 < (R - ‖p‖) ^ 2 * u p :=
    lt_of_lt_of_le (mul_pos (sq_pos_of_pos hR) hzero) hFp
  have hpd : ‖p‖ < R := by
    apply lt_of_le_of_ne hpR
    intro heq
    rw [heq, sub_self, zero_pow (by norm_num), zero_mul] at hFpos
    exact (lt_irrefl 0 hFpos)
  have hup : 0 < u p := by
    by_contra h
    have := hnonneg p hp
    have heq : u p = 0 := le_antisymm (le_of_not_gt h) this
    exact (lt_irrefl (0 : ℝ)) (by simpa only [heq, mul_zero] using hFpos)
  let s : ℝ := (R - ‖p‖) / 2
  have hs : 0 < s := by dsimp only [s]; linarith
  have hsR : s ≤ R / 2 := by dsimp only [s]; linarith [norm_nonneg p]
  have hnorm (x : E) (hx : x ∈ Metric.closedBall p s) : ‖x‖ ≤ ‖p‖ + s := by
    have hd : ‖x - p‖ ≤ s := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have ht : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - p) p
    linarith
  have hsub : Metric.closedBall p s ⊆ Metric.ball 0 R := by
    intro x hx
    have hxnorm := hnorm x hx
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp only [s] at hxnorm
    linarith
  refine ⟨p, s, hs, hsR, hup, hsub, ?_, ?_⟩
  · dsimp only [s]
    nlinarith only [hFp]
  · intro x hx
    have hxR := Metric.ball_subset_closedBall (hsub hx)
    have hux := hnonneg x hxR
    have hm : (R - ‖x‖) ^ 2 * u x ≤ (R - ‖p‖) ^ 2 * u p := hmax hxR
    have hmarg : s ≤ R - ‖x‖ := by
      have hn := hnorm x hx
      dsimp only [s] at *
      linarith
    have hsq : s ^ 2 ≤ (R - ‖x‖) ^ 2 := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hsq hux
    have hpe : (R - ‖p‖) ^ 2 = 4 * s ^ 2 := by dsimp only [s]; ring
    rw [hpe] at hm
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp (by nlinarith only [hb, hm])

end PoincareConjecture.M60
