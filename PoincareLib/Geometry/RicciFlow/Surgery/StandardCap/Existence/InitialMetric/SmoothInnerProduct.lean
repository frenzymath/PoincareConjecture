import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.InnerProduct
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.RoundTipSeries
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smoothness of the actual cap inner product

This completes the tip smoothness step in Morgan-Tian Lemma 12.2,
printed pp. 294-295. At positive radius, ordinary smooth calculus applies.
At the origin, the exact spherical profile agrees with analytic functions
of the smooth squared norm, including the correct removable values.
See `proof-work/tasks/M34/derivations/tip-smoothness.md`.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M34

/-- Exact agreement of the angular metric coefficient with its analytic
round extension before the cutoff (Lemma 12.2, p. 294). -/
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

/-- Exact agreement of the radial correction with its analytic round
extension before the cutoff (Lemma 12.2, p. 294). -/
theorem capRadialCoefficient_eq_round {a r : ℝ} (ha : 0 ≤ a) (hr : r ≤ a) :
    capRadialCoefficient a r = roundTipRadial (r ^ 2) := by
  by_cases h : r = 0
  · simp only [h, capRadialCoefficient, if_true, zero_pow (by decide : 2 ≠ 0),
      roundTipRadial_zero]
  · rw [capRadialCoefficient, if_neg h, capAngularCoefficient_eq_round ha hr,
      roundTipRadial_sq h]

/-- Smoothness of the scalar angular coefficient off its removable
point (Lemma 12.2, pp. 294-295). -/
theorem capAngularCoefficient_contDiffAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (capAngularCoefficient a) r := by
  apply (((capProfile_contDiff a).contDiffAt.div contDiffAt_id hr).pow 2).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact if_neg hs

/-- Smoothness of the scalar radial correction off its removable
point (Lemma 12.2, pp. 294-295). -/
theorem capRadialCoefficient_contDiffAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (capRadialCoefficient a) r := by
  apply (((contDiffAt_const (c := (1 : ℝ))).sub (capAngularCoefficient_contDiffAt a hr)).div
    (contDiffAt_id.pow 2) (pow_ne_zero 2 hr)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hr] with s hs
  exact if_neg hs

/-- Smoothness of the angular coefficient as a function on all of
Euclidean three-space, including the origin (Lemma 12.2, p. 294). -/
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

/-- Smoothness of the radial correction as a function on all of
Euclidean three-space, including its nonzero limiting value at the tip
(Lemma 12.2, p. 294). -/
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

/-- Smoothness into the normed space of actual continuous bilinear maps,
not just separate scalar coefficients (Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (capMetricInner a) := by
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := innerSL ℝ
  have : IsBoundedSMul ℝ (StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)
  exact ((capAngularCoefficient_norm_contDiff ha).smul (contDiff_const (c := B))).add
    ((capRadialCoefficient_norm_contDiff ha).smul (B.contDiff.smulRight B.contDiff))

end PoincareMT.M34
