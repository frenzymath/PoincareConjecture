import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A smooth radial profile for the initial cap

The profile in Morgan-Tian Lemma 12.2, printed pp. 293-295, is constructed
here in meridian arclength by cutting off the round-sphere slope. The
geometric change from arclength to the book's axial graph coordinate is
derived in `proof-work/tasks/M34/derivations/radial-profile.md`.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT.M34

/-- The decreasing smooth cutoff for Lemma 12.2, pp. 294-295. -/
noncomputable def capCutoff (s : ℝ) : ℝ := 1 - Real.smoothTransition (2 * s)

/-- Smoothness of the cutoff in Lemma 12.2, pp. 294-295. -/
theorem capCutoff_contDiff : ContDiff ℝ ∞ capCutoff := by
  unfold capCutoff
  fun_prop

/-- The cutoff is nonnegative, as required in Lemma 12.2, p. 295. -/
theorem capCutoff_nonneg (s : ℝ) : 0 ≤ capCutoff s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

/-- The cutoff is at most one (Lemma 12.2, p. 295). -/
theorem capCutoff_le_one (s : ℝ) : capCutoff s ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

/-- The cutoff leaves the round tip unchanged (Lemma 12.2, p. 295). -/
theorem capCutoff_eq_one {s : ℝ} (hs : s ≤ 0) : capCutoff s = 1 := by
  rw [capCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- The cutoff vanishes past half a unit (Lemma 12.2, p. 295). -/
theorem capCutoff_eq_zero {s : ℝ} (hs : 1 / 2 ≤ s) : capCutoff s = 0 := by
  rw [capCutoff, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

/-- The explicit cutoff is positive before its terminal plateau
(Lemma 12.2, p. 295). -/
theorem capCutoff_pos {s : ℝ} (hs : s < 1 / 2) : 0 < capCutoff s :=
  sub_pos.mpr (Real.smoothTransition.lt_one_of_lt_one (by linarith))

/-- Monotonicity needed to preserve concavity in Lemma 12.2, p. 295. -/
theorem capCutoff_antitone : Antitone capCutoff := by
  intro s t hst
  exact sub_le_sub_left (Real.smoothTransition.monotone (by linarith)) 1

/-- The radial slope of the round sphere with its distant part cut off;
see Lemma 12.2, pp. 294-295, and the radial-profile derivation. -/
noncomputable def capSlope (a r : ℝ) : ℝ := Real.cos (r / 2) * capCutoff (r - a)

/-- Joint smoothness of the radial slope and cutoff translation
(Lemma 12.2, p. 295). -/
theorem capSlope_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => capSlope p.1 p.2) := by
  unfold capSlope capCutoff
  fun_prop

/-- Smoothness at a fixed translation (Lemma 12.2, p. 295). -/
theorem capSlope_contDiff_right (a : ℝ) : ContDiff ℝ ∞ (capSlope a) := by
  unfold capSlope capCutoff
  fun_prop

/-- The radial slope vanishes on the cylindrical part (Lemma 12.2, p. 295). -/
theorem capSlope_eq_zero {a r : ℝ} (hr : a + 1 / 2 ≤ r) : capSlope a r = 0 := by
  rw [capSlope, capCutoff_eq_zero (by linarith), mul_zero]

/-- Before the cutoff the slope is exactly that of the radius-two sphere
(Lemma 12.2, pp. 294-295). -/
theorem capSlope_eq_cos {a r : ℝ} (hr : r ≤ a) : capSlope a r = Real.cos (r / 2) := by
  rw [capSlope, capCutoff_eq_one (sub_nonpos.mpr hr), mul_one]

/-- The cutoff acts before the cosine can change sign
(Lemma 12.2, pp. 294-295, in radial arclength). -/
theorem capSlope_nonneg {a r : ℝ} (ha : a ≤ Real.pi / 2) (hr : 0 ≤ r) :
    0 ≤ capSlope a r := by
  by_cases h : a + 1 / 2 ≤ r
  · rw [capSlope_eq_zero h]
  · have hrpi : r < Real.pi := by linarith [Real.pi_gt_three]
    exact mul_nonneg (Real.cos_nonneg_of_mem_Icc (by constructor <;> linarith [Real.pi_pos]))
      (capCutoff_nonneg _)

/-- The radial speed never exceeds one (Lemma 12.2, pp. 294-295). -/
theorem capSlope_le_one (a r : ℝ) : capSlope a r ≤ 1 := by
  calc
    capSlope a r ≤ 1 * capCutoff (r - a) :=
      mul_le_mul_of_nonneg_right (Real.cos_le_one _) (capCutoff_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using capCutoff_le_one (r - a)

/-- The radial slope is nonincreasing on the geometric half-line,
giving a concave profile (Lemma 12.2, pp. 294-295). -/
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

/-- Integrating the slope gives the radial warping function used in
Lemma 12.2, pp. 294-295. The integral has no singular endpoint. -/
noncomputable def capProfile (a r : ℝ) : ℝ := ∫ s in 0..r, capSlope a s

/-- The radial profile has the prescribed slope (Lemma 12.2, p. 295). -/
theorem capProfile_hasDerivAt (a r : ℝ) : HasDerivAt (capProfile a) (capSlope a r) r := by
  have hc := (capSlope_contDiff_right a).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousAt

/-- The classical derivative agrees with the prescribed smooth slope
(Lemma 12.2, p. 295). -/
theorem capProfile_deriv (a : ℝ) : deriv (capProfile a) = capSlope a := by
  funext r
  exact (capProfile_hasDerivAt a r).deriv

/-- The radial profile is smooth, including at radius zero
(Lemma 12.2, pp. 294-295). -/
theorem capProfile_contDiff (a : ℝ) : ContDiff ℝ ∞ (capProfile a) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r => (capProfile_hasDerivAt a r).differentiableAt, ?_⟩
  rw [capProfile_deriv]
  exact capSlope_contDiff_right a

/-- The profile vanishes at the tip (Lemma 12.2, p. 294). -/
theorem capProfile_zero (a : ℝ) : capProfile a 0 = 0 := by
  simp [capProfile]

/-- Continuity of the plateau height in the cutoff translation, for the
intermediate-value argument of Lemma 12.2, p. 295. -/
theorem capProfile_continuous_parameter (r : ℝ) : Continuous (fun a => capProfile a r) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    capSlope_contDiff.continuous 0 r

end PoincareMT.M34
