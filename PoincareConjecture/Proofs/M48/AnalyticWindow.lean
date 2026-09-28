import PoincareConjecture.Definitions.M48AnalyticCalibration
import PoincareConjecture.Definitions.M48EpochExtension

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

theorem SurgeryPrefixControls.delta_le_initial
    {S : RepairedControlledSchedulesData.{u}} {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hp : S.SeedCompatible p)
    (t : ℝ) (ht : 0 ≤ t) : F.parameters.delta t ≤ S.Delta0 := by
  have hzero : (0 : ℝ) ∈ surgeryEpochEntry 0 := by
    change (0 : ℝ) ≤ 0 ∧ 0 < (2 : ℝ) ^ 0 / 32
    norm_num
  have hbound := old.delta_bound 0 (Nat.zero_le _) 0
    ⟨⟨le_rfl, O.H_pos⟩, hzero⟩
  exact (F.parameters.delta_antitone (by simpa only [Set.mem_Ici] using (le_refl (0 : ℝ)))
    (by simpa only [Set.mem_Ici] using ht) ht).trans (hbound.trans_eq hp.Delta_zero_eq)

namespace M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)

noncomputable def limitRadius (r : ℝ) : ℝ :=
  min r (A.component.curvature_threshold + 1)⁻¹

theorem limitRadius_pos {r : ℝ} (hr : 0 < r) : 0 < A.limitRadius r := by
  apply lt_min hr
  apply inv_pos.mpr
  linarith [A.component.one_le_curvature_threshold]

theorem limitRadius_le (r : ℝ) : A.limitRadius r ≤ r := min_le_left _ _

theorem threshold_bounds {r Q : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (hQ : (A.limitRadius r)⁻¹ ^ 2 ≤ Q) :
    A.component.curvature_threshold ≤ Q ∧ (40000 : ℝ) ≤ Q := by
  have hr0 := A.limitRadius_pos hr
  have hsmall : A.limitRadius r ≤ (1 : ℝ) / 200 :=
    (A.limitRadius_le r).trans (hre.trans (S.setup.epsilon_le.trans (min_le_left _ _)))
  have hi := one_div_le_one_div_of_le hr0 hsmall
  norm_num [one_div] at hi
  have hlarge := one_div_le_one_div_of_le hr0
    (show A.limitRadius r ≤ (A.component.curvature_threshold + 1)⁻¹ from min_le_right _ _)
  simp only [one_div, inv_inv] at hlarge
  have hs : (A.component.curvature_threshold + 1) ^ 2 ≤ (A.limitRadius r)⁻¹ ^ 2 := by
    gcongr
    linarith [A.component.one_le_curvature_threshold]
  constructor
  · nlinarith [A.component.one_le_curvature_threshold]
  · nlinarith

theorem component_window {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {r t : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (ht : t ∈ surgeryObservationInterval O) (x : (F.slice t).carrier)
    (hQ : (A.limitRadius r)⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x) :
    Icc (t - A.component.duration / (F.connection t).scalarCurvature x) t ⊆
      surgeryObservationInterval O := by
  have hlarge := (A.threshold_bounds hr hre hQ).2
  have htlate : (1 : ℝ) / 16 < t := by
    by_contra h
    have hbound := ((S.calibration.initial_capture F).2 t
      (O.interval_subset ht) (le_of_not_gt h) x).2.1
    nlinarith [le_abs_self ((F.connection t).scalarCurvature x)]
  have hduration : A.component.duration / (F.connection t).scalarCurvature x ≤
      (1 : ℝ) / 40000 := by
    calc
      _ ≤ 1 / (F.connection t).scalarCurvature x :=
        div_le_div_of_nonneg_right A.component.duration_le_one (by linarith)
      _ ≤ 1 / 40000 := one_div_le_one_div_of_le (by norm_num) hlarge
  intro s hs
  exact ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩

theorem cut_scale_lt_radius
    {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (old : SurgeryPrefixControls p F O)
    (hp : S.SeedCompatible p) {r : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (t : ℝ) (ht : 0 ≤ t) : F.parameters.delta t * r < A.limitRadius r := by
  have hdelta := old.delta_le_initial hp t ht
  have hdelta_pos := F.parameters.delta_pos t ht
  have hepsilon : S.setup.epsilon ≤ (1 : ℝ) / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  have hD : S.Delta0 ≤ S.calibration.beta * S.setup.epsilon / 3 :=
    S.calibration.delta_zero_eq.le.trans (min_le_left _ _)
  have hD1 : S.Delta0 < 1 := by
    have hprod := mul_lt_mul_of_pos_right S.calibration.beta_lt_half S.setup.epsilon_pos
    nlinarith
  have hrho : F.parameters.delta t * r ≤ S.Delta0 * S.setup.epsilon :=
    (mul_le_mul_of_nonneg_left hre hdelta_pos.le).trans
      (mul_le_mul_of_nonneg_right hdelta S.setup.epsilon_pos.le)
  have ha : 0 < (A.component.curvature_threshold + 1)⁻¹ := by
    apply inv_pos.mpr
    linarith [A.component.one_le_curvature_threshold]
  apply lt_min
  · simpa only [one_mul] using mul_lt_mul_of_pos_right (hdelta.trans_lt hD1) hr
  · nlinarith [A.delta_radius]

end M48AnalyticCalibration

end PoincareConjecture
