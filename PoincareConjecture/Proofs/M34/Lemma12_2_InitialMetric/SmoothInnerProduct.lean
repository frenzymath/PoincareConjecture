import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.InnerProduct
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RoundTipSeries
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M34

theorem capAngularCoefficient_eq_round {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    capAngularCoefficient a r = roundTipAngular (r ^ 2) := by
  by_cases h : r = 0
  · simp only [h, capAngularCoefficient, if_true, zero_pow (by decide : 2 ≠ 0),
      roundTipAngular_zero]
  · rw [capAngularCoefficient, if_neg h, capProfile_eq_round ha hr, roundTipAngular_sq h]
    have hc := Real.cos_two_mul (r / 2)
    rw [show 2 * (r / 2) = r by ring] at hc
    have hs := Real.sin_sq_add_cos_sq (r / 2)
    field_simp
    nlinarith

theorem capRadialCoefficient_eq_round {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    capRadialCoefficient a r = roundTipRadial (r ^ 2) := by
  by_cases h : r = 0
  · simp only [h, capRadialCoefficient, if_true, zero_pow (by decide : 2 ≠ 0),
      roundTipRadial_zero]
  · rw [capRadialCoefficient, if_neg h, capAngularCoefficient_eq_round ha hr,
      roundTipRadial_sq h]

theorem capAngularCoefficient_contDiffAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (capAngularCoefficient a) r := by
  apply (((capProfile_contDiff a).contDiffAt.div contDiffAt_id hr).pow 2).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact if_neg hs

theorem capRadialCoefficient_contDiffAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (capRadialCoefficient a) r := by
  apply (((contDiffAt_const (c := (1 : ℝ))).sub (capAngularCoefficient_contDiffAt a hr)).div
    (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact if_neg hs

theorem capAngularCoefficient_norm_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (fun x : StandardCapSpace => capAngularCoefficient a ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hs : ContDiffAt ℝ ∞ roundTipAngular (‖(0 : StandardCapSpace)‖ ^ 2) := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        roundTipAngular_analyticAt.contDiffAt (n := ∞)
    apply (hs.comp 0 (contDiffAt_id.norm_sq ℝ)).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : StandardCapSpace) ha] with y hy
    exact capAngularCoefficient_eq_round ha.le
      (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy))
  · exact (capAngularCoefficient_contDiffAt a (norm_ne_zero_iff.mpr hx)).comp x
      (contDiffAt_norm ℝ hx)

theorem capRadialCoefficient_norm_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (fun x : StandardCapSpace => capRadialCoefficient a ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hs : ContDiffAt ℝ ∞ roundTipRadial (‖(0 : StandardCapSpace)‖ ^ 2) := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        roundTipRadial_analyticAt.contDiffAt (n := ∞)
    apply (hs.comp 0 (contDiffAt_id.norm_sq ℝ)).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : StandardCapSpace) ha] with y hy
    exact capRadialCoefficient_eq_round ha.le
      (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hy))
  · exact (capRadialCoefficient_contDiffAt a (norm_ne_zero_iff.mpr hx)).comp x
      (contDiffAt_norm ℝ hx)

theorem capMetricInner_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (capMetricInner a) := by
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := innerSL ℝ
  have : IsBoundedSMul ℝ (StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)
  exact ((capAngularCoefficient_norm_contDiff ha).smul (contDiff_const (c := B))).add
    ((capRadialCoefficient_norm_contDiff ha).smul (B.contDiff.smulRight B.contDiff))

end PoincareConjecture.M34
