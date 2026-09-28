import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture

noncomputable def smoothWidthProfile (r : ℝ → ℝ) (a w s : ℝ) : ℝ :=
  Real.exp (-(∫ v in a..s, r v / 2)) *
    (w - 2 * Real.pi * ∫ v in a..s, Real.exp (∫ x in a..v, r x / 2))

theorem smoothWidthProfile_initial (r : ℝ → ℝ) (a w : ℝ) :
    smoothWidthProfile r a w a = w := by
  simp [smoothWidthProfile]

theorem smoothWidthProfile_hasDerivWithinAt {r : ℝ → ℝ} {a b w : ℝ}
    (hab : a ≤ b) (hr : ContinuousOn r (Icc a b)) :
    HasDerivWithinAt (smoothWidthProfile r a w)
      (-2 * Real.pi - r a / 2 * w) (Icc a b) a := by
  let : Fact (a ∈ Icc a b) := ⟨⟨le_rfl, hab⟩⟩
  have hc : ContinuousOn (fun x => r x / 2) (Icc a b) := hr.div_const 2
  have hi : IntervalIntegrable (fun x => r x / 2) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hd : HasDerivWithinAt (fun s => ∫ v in a..s, r v / 2)
      (r a / 2) (Icc a b) a :=
    intervalIntegral.integral_hasDerivWithinAt_right (by simp)
      (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc a)
      (hc a ⟨le_rfl, hab⟩)
  have hp : ContinuousOn (fun s => ∫ v in a..s, r v / 2) (Icc a b) := by
    simpa [uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : a ∈ uIcc a b))
  have he := Real.continuous_exp.comp_continuousOn hp
  have hde : HasDerivWithinAt
      (fun s => ∫ v in a..s, Real.exp (∫ x in a..v, r x / 2))
      1 (Icc a b) a := by
    simpa using intervalIntegral.integral_hasDerivWithinAt_right (a := a) (b := a)
      (by simp : IntervalIntegrable
        (fun v => Real.exp (∫ x in a..v, r x / 2)) volume a a)
      (he.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc a)
      (he a ⟨le_rfl, hab⟩)
  have hprofile := hd.neg.exp.mul ((hasDerivWithinAt_const a (Icc a b) w).sub
    (hde.const_mul (2 * Real.pi)))
  simp only [Pi.neg_apply, Pi.sub_apply, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one,
    mul_zero, sub_zero, one_mul, zero_sub] at hprofile
  have heq : -(r a / 2) * w + -(2 * Real.pi) = -2 * Real.pi - r a / 2 * w := by ring
  rw [heq] at hprofile
  exact hprofile

theorem smoothWidthProfile_forward_bound {r : ℝ → ℝ} {a b w : ℝ}
    (hab : a ≤ b) (hr : ContinuousOn r (Icc a b))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc a b, a < s → s < a + delta →
      (smoothWidthProfile r a w s - w) / (s - a) ≤
        -2 * Real.pi - r a / 2 * w + epsilon := by
  have h := (smoothWidthProfile_hasDerivWithinAt (w := w) hab hr).limsup_slope_le
    (lt_add_of_pos_right _ hepsilon)
  rcases Metric.mem_nhdsWithin_iff.mp h with ⟨delta, hdelta, hball⟩
  refine ⟨delta, hdelta, ?_⟩
  intro s hs has hsd
  have hsball : s ∈ Metric.ball a delta := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr has)]
    linarith
  have hbound := hball ⟨hsball, hs, by simpa using ne_of_gt has⟩
  change slope (smoothWidthProfile r a w) a s < _ at hbound
  rw [slope_def_field, smoothWidthProfile_initial] at hbound
  exact hbound.le

end PoincareConjecture
