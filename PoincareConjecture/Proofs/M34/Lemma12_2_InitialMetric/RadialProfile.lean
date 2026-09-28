import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M34

noncomputable def capCutoff (s : ℝ) : ℝ := 1 - Real.smoothTransition (2 * s)

theorem capCutoff_contDiff : ContDiff ℝ ∞ capCutoff := by
  unfold capCutoff
  fun_prop

theorem capCutoff_nonneg (s : ℝ) : 0 ≤ capCutoff s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem capCutoff_le_one (s : ℝ) : capCutoff s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem capCutoff_eq_one {s : ℝ} (hs : s ≤ 0) : capCutoff s = 1 := by
  rw [capCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem capCutoff_eq_zero {s : ℝ} (hs : 1 / 2 ≤ s) : capCutoff s = 0 := by
  rw [capCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem capCutoff_pos {s : ℝ} (hs : s < 1 / 2) : 0 < capCutoff s :=
  sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by linarith))

theorem capCutoff_antitone : Antitone capCutoff := by
  intro s t hst
  exact sub_le_sub_left (Real.smoothTransition.monotone (by linarith)) 1

noncomputable def capSlope (a r : ℝ) : ℝ := Real.cos (r / 2) * capCutoff (r - a)

theorem capSlope_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => capSlope p.1 p.2) := by
  unfold capSlope capCutoff
  fun_prop

theorem capSlope_contDiff_right (a : ℝ) : ContDiff ℝ ∞ (capSlope a) := by
  unfold capSlope capCutoff
  fun_prop

theorem capSlope_eq_zero {a r : ℝ} (hr : a + 1 / 2 ≤ r) : capSlope a r = 0 := by
  rw [capSlope, capCutoff_eq_zero (by linarith), mul_zero]

theorem capSlope_eq_cos {a r : ℝ} (hr : r ≤ a) : capSlope a r = Real.cos (r / 2) := by
  rw [capSlope, capCutoff_eq_one (sub_nonpos.mpr hr), mul_one]

theorem capSlope_nonneg {a r : ℝ} (ha : a ≤ Real.pi / 2) (hr : 0 ≤ r) :
    0 ≤ capSlope a r := by
  by_cases h : a + 1 / 2 ≤ r
  · rw [capSlope_eq_zero h]
  · have hrpi : r < Real.pi := by linarith [Real.pi_gt_three]
    exact mul_nonneg (Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos]))
      (capCutoff_nonneg _)

theorem capSlope_le_one (a r : ℝ) : capSlope a r ≤ 1 := by
  calc
    capSlope a r ≤ 1 * capCutoff (r - a) :=
      mul_le_mul_of_nonneg_right (Real.cos_le_one _) (capCutoff_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using capCutoff_le_one (r - a)

theorem capSlope_antitoneOn {a : ℝ} (ha : a ≤ Real.pi / 2) :
    AntitoneOn (capSlope a) (Ici 0) := by
  intro r hr s hs hrs
  change 0 ≤ r at hr
  change 0 ≤ s at hs
  by_cases h : a + 1 / 2 ≤ s
  · rw [capSlope_eq_zero h]
    exact capSlope_nonneg ha hr
  · have hspi : s < Real.pi := by linarith [Real.pi_gt_three]
    apply mul_le_mul
    · exact Real.antitoneOn_cos (by constructor <;> linarith)
        (by constructor <;> linarith) (by linarith)
    · exact capCutoff_antitone (sub_le_sub_right hrs _)
    · exact capCutoff_nonneg _
    · exact Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos])

noncomputable def capProfile (a r : ℝ) : ℝ := ∫ s in 0..r, capSlope a s

theorem capProfile_hasDerivAt (a r : ℝ) : HasDerivAt (capProfile a) (capSlope a r) r := by
  have hc := (capSlope_contDiff_right a).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousAt

theorem capProfile_deriv (a : ℝ) : deriv (capProfile a) = capSlope a := by
  funext r
  exact (capProfile_hasDerivAt a r).deriv

theorem capProfile_contDiff (a : ℝ) : ContDiff ℝ ∞ (capProfile a) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (capProfile_hasDerivAt a r).differentiableAt, ?_⟩
  rw [capProfile_deriv]
  exact capSlope_contDiff_right a

theorem capProfile_zero (a : ℝ) : capProfile a 0 = 0 := by
  simp [capProfile]

theorem capProfile_continuous_parameter (r : ℝ) : Continuous (fun a => capProfile a r) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    capSlope_contDiff.continuous 0 r

end PoincareConjecture.M34
