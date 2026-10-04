import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Plateau
import Mathlib.Analysis.Convex.Deriv

/-!
# Shape bounds for the standard cap profile

These are the arclength versions of the profile inequalities in
Morgan-Tian Lemma 12.2, printed pp. 294-295. All sign and concavity
claims are restricted to nonnegative radii. In particular, the later
curvature formulas may divide by the profile only at positive radii.
See `proof-work/tasks/M34/derivations/radial-profile.md`.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT.M34

/-- The cap is round to first order at its tip (Lemma 12.2, p. 294). -/
theorem capSlope_zero {a : ℝ} (ha : 0 ≤ a) : capSlope a 0 = 1 := by
  rw [capSlope_eq_cos ha, zero_div, Real.cos_zero]

/-- Away from zero the radial speed is strictly less than one
(Lemma 12.2, pp. 294-295, arclength derivation). -/
theorem capSlope_lt_one {a r : ℝ} (ha : a ≤ Real.pi / 2) (hr : 0 < r) :
    capSlope a r < 1 := by
  by_cases h : a + 1 / 2 ≤ r
  · rw [capSlope_eq_zero h]
    norm_num
  · have hrpi : r < Real.pi := by linarith [Real.pi_gt_three]
    have hc : 0 ≤ Real.cos (r / 2) :=
      Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos])
    calc
      capSlope a r ≤ Real.cos (r / 2) * 1 :=
        mul_le_mul_of_nonneg_left (capCutoff_le_one _) hc
      _ < 1 := by
        simpa only [mul_one, Real.cos_zero] using
          Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (by rfl)
            (by linarith) (by linarith)

/-- The second derivative is nonpositive, including at zero.
Smoothness and the unique derivative on the half-line justify the
one-sided monotonicity argument (Lemma 12.2, pp. 294-295). -/
theorem capSlope_deriv_nonpos {a r : ℝ} (ha : a ≤ Real.pi / 2) (hr : 0 ≤ r) :
    deriv (capSlope a) r ≤ 0 := by
  have hd := (capSlope_contDiff_right a).differentiable (by simp)
  rw [← hd.differentiableAt.derivWithin (uniqueDiffOn_Ici 0 r hr)]
  exact (capSlope_antitoneOn ha).derivWithin_nonpos

/-- The profile is nondecreasing on nonnegative radii
(Lemma 12.2, pp. 294-295). -/
theorem capProfile_monotoneOn {a : ℝ} (ha : a ≤ Real.pi / 2) :
    MonotoneOn (capProfile a) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (capProfile_contDiff a).continuous.continuousOn
    ((capProfile_contDiff a).differentiable (by simp)).differentiableOn
  intro r hr
  rw [capProfile_deriv]
  exact capSlope_nonneg ha (interior_subset hr)

/-- Concavity on the geometric half-line is the curvature sign condition
in Lemma 12.2, pp. 294-295. -/
theorem capProfile_concaveOn {a : ℝ} (ha : a ≤ Real.pi / 2) :
    ConcaveOn ℝ (Ici 0) (capProfile a) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (capProfile_contDiff a).continuous.continuousOn
    ((capProfile_contDiff a).differentiable (by simp)).differentiableOn
  rw [capProfile_deriv]
  exact (capSlope_antitoneOn ha).mono interior_subset

/-- Positivity of the profile away from the tip, before any curvature
expression uses its reciprocal (Lemma 12.2, p. 295). -/
theorem capProfile_pos {a r : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (hr : 0 < r) : 0 < capProfile a r := by
  apply intervalIntegral.integral_pos hr (capSlope_contDiff_right a).continuous.continuousOn
  · intro x hx
    exact capSlope_nonneg hapi hx.1.le
  · exact ⟨0, ⟨le_rfl, hr.le⟩, by rw [capSlope_zero ha]; norm_num⟩

/-- Radial speed at most one bounds the angular radius by arclength
(Lemma 12.2, pp. 294-295). -/
theorem capProfile_le_radius (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : capProfile a r ≤ r := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hr
    ((capSlope_contDiff_right a).continuous.intervalIntegrable 0 r)
    (continuous_const.intervalIntegrable 0 r) (fun x _ => capSlope_le_one a x)
  simpa only [capProfile, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one] using h

/-- The normalized cap has exactly cylindrical radius beyond its cutoff
(Lemma 12.2, p. 295). -/
theorem capProfile_eq_sqrt_two {a r : ℝ} (ha : a ≤ Real.pi / 2)
    (hn : capProfile a Real.pi = Real.sqrt 2) (hr : a + 1 / 2 ≤ r) :
    capProfile a r = Real.sqrt 2 := by
  rw [capProfile_eq_of_ge (s := Real.pi) hr (by linarith [Real.pi_gt_three]), hn]

/-- The profile never exceeds its normalized cylindrical radius
(Lemma 12.2, p. 295). -/
theorem capProfile_le_sqrt_two {a r : ℝ} (ha : a ≤ Real.pi / 2)
    (hn : capProfile a Real.pi = Real.sqrt 2) (hr : 0 ≤ r) :
    capProfile a r ≤ Real.sqrt 2 := by
  by_cases h : a + 1 / 2 ≤ r
  · exact (capProfile_eq_sqrt_two ha hn h).le
  · rw [← hn]
    exact capProfile_monotoneOn ha hr Real.pi_pos.le (by linarith [Real.pi_gt_three])

end PoincareMT.M34
