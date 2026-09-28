import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Plateau
import Mathlib.Analysis.Convex.Deriv











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M34


theorem capSlope_zero {a : ℝ} (ha : 0 ≤ a) : capSlope a 0 = 1 := by
  rw [capSlope_eq_cos ha, zero_div, Real.cos_zero]



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




theorem capSlope_deriv_nonpos {a r : ℝ} (ha : a ≤ Real.pi / 2) (hr : 0 ≤ r) :
    deriv (capSlope a) r ≤ 0 := by
  have hd := (capSlope_contDiff_right a).differentiable (by simp)
  rw [← hd.differentiableAt.derivWithin (uniqueDiffOn_Ici 0 r hr)]
  exact (capSlope_antitoneOn ha).derivWithin_nonpos



theorem capProfile_monotoneOn {a : ℝ} (ha : a ≤ Real.pi / 2) :
    MonotoneOn (capProfile a) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (capProfile_contDiff a).continuous.continuousOn
    ((capProfile_contDiff a).differentiable (by simp)).differentiableOn
  intro r hr
  rw [capProfile_deriv]
  exact capSlope_nonneg ha (interior_subset hr)



theorem capProfile_concaveOn {a : ℝ} (ha : a ≤ Real.pi / 2) :
    ConcaveOn ℝ (Ici 0) (capProfile a) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (capProfile_contDiff a).continuous.continuousOn
    ((capProfile_contDiff a).differentiable (by simp)).differentiableOn
  rw [capProfile_deriv]
  exact (capSlope_antitoneOn ha).mono interior_subset



theorem capProfile_pos {a r : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (hr : 0 < r) : 0 < capProfile a r := by
  apply intervalIntegral.integral_pos hr (capSlope_contDiff_right a).continuous.continuousOn
  · intro x hx
    exact capSlope_nonneg hapi hx.1.le
  · exact ⟨0, ⟨le_rfl, hr.le⟩, by rw [capSlope_zero ha]; norm_num⟩



theorem capProfile_le_radius (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : capProfile a r ≤ r := by
  have h := intervalIntegral.integral_mono_on (μ := volume) hr
    ((capSlope_contDiff_right a).continuous.intervalIntegrable 0 r)
    (continuous_const.intervalIntegrable 0 r) (fun x _ => capSlope_le_one a x)
  simpa only [capProfile, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one] using h



theorem capProfile_eq_sqrt_two {a r : ℝ} (ha : a ≤ Real.pi / 2)
    (hn : capProfile a Real.pi = Real.sqrt 2) (hr : a + 1 / 2 ≤ r) :
    capProfile a r = Real.sqrt 2 := by
  rw [capProfile_eq_of_ge (s := Real.pi) hr (by linarith [Real.pi_gt_three]), hn]



theorem capProfile_le_sqrt_two {a r : ℝ} (ha : a ≤ Real.pi / 2)
    (hn : capProfile a Real.pi = Real.sqrt 2) (hr : 0 ≤ r) :
    capProfile a r ≤ Real.sqrt 2 := by
  by_cases h : a + 1 / 2 ≤ r
  · exact (capProfile_eq_sqrt_two ha hn h).le
  · rw [← hn]
    exact capProfile_monotoneOn ha hr Real.pi_pos.le (by linarith [Real.pi_gt_three])

end PoincareConjecture.M34
