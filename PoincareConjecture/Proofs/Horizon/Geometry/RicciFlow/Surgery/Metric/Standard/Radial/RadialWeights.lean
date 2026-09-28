import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Collapse.PolarInverse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Profile.SmoothProfile








set_option autoImplicit false

open scoped ContDiff Topology

namespace PoincareConjecture.MetricSurgery

noncomputable def standardSurgeryHeight (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : ℝ :=
  g₀.cylindrical_end.radius + 4 - radialArclength g₀ ‖x‖

theorem standardSurgeryHeight_continuous (g₀ : StandardInitialMetric) :
    Continuous (standardSurgeryHeight g₀) :=
  continuous_const.sub ((radialArclength_contDiff g₀).continuous.comp continuous_norm)

theorem standardSurgeryHeight_contDiffAt (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (standardSurgeryHeight g₀) x :=
  contDiffAt_const.sub ((radialArclength_contDiff g₀).contDiffAt.comp x (contDiffAt_norm ℝ hx))

@[simp]
theorem standardSurgeryHeight_zero (g₀ : StandardInitialMetric) :
    standardSurgeryHeight g₀ 0 = g₀.cylindrical_end.radius + 4 := by
  simp [standardSurgeryHeight, radialArclength_zero]

noncomputable def radialNeckWeight (g₀ : StandardInitialMetric) (x : StandardCapSpace) : ℝ :=
  neckCutoff (standardSurgeryHeight g₀ x)

noncomputable def radialTipWeight (g₀ : StandardInitialMetric) (r : ℝ)
    (x : StandardCapSpace) : ℝ :=
  tipCutoff (g₀.cylindrical_end.radius + 4) r (standardSurgeryHeight g₀ x)

theorem radialNeckWeight_eventually_zero (g₀ : StandardInitialMetric) :
    radialNeckWeight g₀ =ᶠ[nhds 0] fun _ => 0 := by
  have hopen : IsOpen {x | (7 / 4 : ℝ) < standardSurgeryHeight g₀ x} :=
    isOpen_lt continuous_const (standardSurgeryHeight_continuous g₀)
  have hzero : (7 / 4 : ℝ) < standardSurgeryHeight g₀ 0 := by
    rw [standardSurgeryHeight_zero]
    linarith [g₀.cylindrical_end.radius_pos]
  filter_upwards [hopen.mem_nhds hzero] with x hx
  exact neckCutoff_eq_zero hx.le

theorem radialTipWeight_eventually_zero (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    radialTipWeight g₀ r =ᶠ[nhds 0] fun _ => 0 := by
  have hopen : IsOpen {x | g₀.cylindrical_end.radius + 4 - r / 2 <
      standardSurgeryHeight g₀ x} :=
    isOpen_lt continuous_const (standardSurgeryHeight_continuous g₀)
  have hzero : g₀.cylindrical_end.radius + 4 - r / 2 < standardSurgeryHeight g₀ 0 := by
    rw [standardSurgeryHeight_zero]
    linarith
  filter_upwards [hopen.mem_nhds hzero] with x hx
  exact tipCutoff_eq_zero hr hx.le

theorem radialNeckWeight_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (radialNeckWeight g₀) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (radialNeckWeight_eventually_zero g₀)
  · exact neckCutoff_contDiff.contDiffAt.comp x (standardSurgeryHeight_contDiffAt g₀ hx)

theorem radialTipWeight_contDiff (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (radialTipWeight g₀ r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq (radialTipWeight_eventually_zero g₀ hr)
  · exact (tipCutoff_contDiff _ r).contDiffAt.comp x (standardSurgeryHeight_contDiffAt g₀ hx)

theorem radialNeckWeight_bounds (g₀ : StandardInitialMetric) (x : StandardCapSpace) :
    0 ≤ radialNeckWeight g₀ x ∧ radialNeckWeight g₀ x ≤ 1 :=
  ⟨neckCutoff_nonneg _, neckCutoff_le_one _⟩

theorem radialTipWeight_bounds (g₀ : StandardInitialMetric) (r : ℝ) (x : StandardCapSpace) :
    0 ≤ radialTipWeight g₀ r x ∧ radialTipWeight g₀ r x ≤ 1 :=
  ⟨tipCutoff_nonneg _ _ _, tipCutoff_le_one _ _ _⟩

theorem radialNeckWeight_tsupport (g₀ : StandardInitialMetric) :
    tsupport (radialNeckWeight g₀) ⊆
      {x | g₀.cylindrical_end.radius + 4 - 7 / 4 ≤ radialArclength g₀ ‖x‖} := by
  apply closure_minimal _ (isClosed_le continuous_const
    ((radialArclength_contDiff g₀).continuous.comp continuous_norm))
  intro x hx
  change radialNeckWeight g₀ x ≠ 0 at hx
  change g₀.cylindrical_end.radius + 4 - 7 / 4 ≤ radialArclength g₀ ‖x‖
  apply le_of_not_gt
  intro hlt
  apply hx
  apply neckCutoff_eq_zero
  dsimp [standardSurgeryHeight]
  linarith

noncomputable def radialConformalMultiplier (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) (x : StandardCapSpace) : ℝ :=
  radialTipWeight g₀ r x * conformalFactor C q epsilon (standardSurgeryHeight g₀ x) +
    (1 - radialTipWeight g₀ r x) * conformalFactor C q epsilon (g₀.cylindrical_end.radius + 4)

theorem radialConformalMultiplier_eventually_constant (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) :
    radialConformalMultiplier g₀ C q epsilon r =ᶠ[nhds 0]
      fun _ => conformalFactor C q epsilon (g₀.cylindrical_end.radius + 4) := by
  filter_upwards [radialTipWeight_eventually_zero g₀ hr] with x hx
  simp [radialConformalMultiplier, hx]

theorem radialConformalMultiplier_contDiff (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (radialConformalMultiplier g₀ C q epsilon r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact contDiffAt_const.congr_of_eventuallyEq
      (radialConformalMultiplier_eventually_constant g₀ C q epsilon hr)
  · exact ((radialTipWeight_contDiff g₀ hr).contDiffAt.mul
      ((conformalFactor_contDiff C q epsilon).contDiffAt.comp x
        (standardSurgeryHeight_contDiffAt g₀ hx))).add
      ((contDiffAt_const.sub (radialTipWeight_contDiff g₀ hr).contDiffAt).mul contDiffAt_const)

theorem radialConformalMultiplier_pos (g₀ : StandardInitialMetric)
    (C q epsilon r : ℝ) (x : StandardCapSpace) :
    0 < radialConformalMultiplier g₀ C q epsilon r x := by
  have hb := radialTipWeight_bounds g₀ r x
  have hnear := conformalFactor_pos C q epsilon (standardSurgeryHeight g₀ x)
  have htip := conformalFactor_pos C q epsilon (g₀.cylindrical_end.radius + 4)
  unfold radialConformalMultiplier
  rcases hb.1.lt_or_eq with hbpos | hbzero
  · exact add_pos_of_pos_of_nonneg (mul_pos hbpos hnear)
      (mul_nonneg (sub_nonneg.mpr hb.2) htip.le)
  · rw [← hbzero]
    simpa using htip

theorem radialTipWeight_eq_one_on_transition (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x : StandardCapSpace} (hx : standardSurgeryHeight g₀ x ≤ 2) :
    radialTipWeight g₀ r x = 1 := by
  apply tipCutoff_eq_one hr
  linarith [g₀.cylindrical_end.radius_pos]

theorem radialConformalMultiplier_eq_on_transition (g₀ : StandardInitialMetric)
    (C q epsilon : ℝ) {r : ℝ} (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x : StandardCapSpace} (hx : standardSurgeryHeight g₀ x ≤ 2) :
    radialConformalMultiplier g₀ C q epsilon r x =
      conformalFactor C q epsilon (standardSurgeryHeight g₀ x) := by
  simp [radialConformalMultiplier, radialTipWeight_eq_one_on_transition g₀ hr hrA hx]

theorem radialConformalMultiplier_eq_one_retained (g₀ : StandardInitialMetric)
    (C epsilon : ℝ) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hrA : r ≤ g₀.cylindrical_end.radius)
    {x : StandardCapSpace} (hx : standardSurgeryHeight g₀ x ≤ 0) :
    radialConformalMultiplier g₀ C q epsilon r x = 1 := by
  rw [radialConformalMultiplier_eq_on_transition g₀ C q epsilon hr hrA (by linarith)]
  exact conformalFactor_eq_one hq hx

end PoincareConjecture.MetricSurgery
