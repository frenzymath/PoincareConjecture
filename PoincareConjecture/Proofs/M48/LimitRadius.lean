import PoincareConjecture.Proofs.M48.AnalyticWindow

set_option autoImplicit false

universe u

namespace PoincareConjecture.M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)

noncomputable def historyRadius (r : ℝ) : ℝ := (3 / 4 : ℝ) * A.limitRadius r

theorem historyRadius_pos {r : ℝ} (hr : 0 < r) : 0 < A.historyRadius r :=
  mul_pos (by norm_num) (A.limitRadius_pos hr)

theorem historyRadius_lt {r : ℝ} (hr : 0 < r) : A.historyRadius r < A.limitRadius r := by
  unfold historyRadius
  nlinarith [A.limitRadius_pos hr]

theorem history_threshold {r : ℝ} (hr : 0 < r) :
    (A.limitRadius r)⁻¹ ^ 2 < (A.historyRadius r)⁻¹ ^ 2 := by
  have hi : (A.limitRadius r)⁻¹ < (A.historyRadius r)⁻¹ :=
    (inv_lt_inv₀ (A.limitRadius_pos hr) (A.historyRadius_pos hr)).2 (A.historyRadius_lt hr)
  nlinarith [inv_pos.mpr (A.limitRadius_pos hr), inv_pos.mpr (A.historyRadius_pos hr)]

theorem cut_scale_lt_historyRadius
    {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (old : SurgeryPrefixControls p F O)
    (hp : S.SeedCompatible p) {r : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (t : ℝ) (ht : 0 ≤ t) : F.parameters.delta t * r < A.historyRadius r := by
  have hdelta := old.delta_le_initial hp t ht
  have hdelta_pos := F.parameters.delta_pos t ht
  have hD : S.Delta0 < (1 : ℝ) / 200 := by
    rw [← hp.Delta_zero_eq]
    exact (p.Delta_le_setup 0).trans_lt S.constants.delta₀_lt
  have hrho : F.parameters.delta t * r ≤ S.Delta0 * S.setup.epsilon :=
    (mul_le_mul_of_nonneg_left hre hdelta_pos.le).trans
      (mul_le_mul_of_nonneg_right hdelta S.setup.epsilon_pos.le)
  have ha : 0 < (A.component.curvature_threshold + 1)⁻¹ := by
    apply inv_pos.mpr
    linarith [A.component.one_le_curvature_threshold]
  have hfirst : F.parameters.delta t * r < (3 / 4 : ℝ) * r := by
    apply mul_lt_mul_of_pos_right (hdelta.trans_lt _) hr
    linarith
  have hsecond : F.parameters.delta t * r <
      (3 / 4 : ℝ) * (A.component.curvature_threshold + 1)⁻¹ := by
    nlinarith [A.delta_radius]
  unfold historyRadius limitRadius
  rcases le_total r (A.component.curvature_threshold + 1)⁻¹ with h | h
  · simpa only [min_eq_left h] using hfirst
  · simpa only [min_eq_right h] using hsecond

end PoincareConjecture.M48AnalyticCalibration
