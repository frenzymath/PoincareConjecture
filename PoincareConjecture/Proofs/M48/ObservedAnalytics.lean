import PoincareConjecture.Proofs.M48.CanonicalAnalytics
import PoincareConjecture.Proofs.M48.AnalyticWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture

namespace M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
  {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
  {O : SurgeryObservation F} (hp : S.SeedCompatible p)
  (old : SurgeryPrefixControls p F O)

include hp old

theorem pointwise {r : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) r)
    (t : ℝ) (ht : t ∈ surgeryObservationInterval O) (x : (F.slice t).carrier)
    (hQ : (A.limitRadius r)⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x) :
    M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
      S.calibration.analytic_constant := by
  have hstd : F.standard_initial = S.setup.standard_initial :=
    old.standard_initial_eq.trans (congrArg SurgeryControlSetup.standard_initial hp.setup_eq)
  have hepsilon : F.parameters.epsilon = S.setup.epsilon :=
    old.epsilon_eq.trans (congrArg SurgeryControlSetup.epsilon hp.setup_eq)
  have hC : F.parameters.C = S.setup.C :=
    old.C_eq.trans (congrArg SurgeryControlSetup.C hp.setup_eq)
  have heps : S.setup.epsilon ≤ (1 : ℝ) / 200 :=
    S.setup.epsilon_le.trans (min_le_left _ _)
  have hinv : r⁻¹ ≤ (A.limitRadius r)⁻¹ :=
    (inv_le_inv₀ hr (A.limitRadius_pos hr)).2 (A.limitRadius_le r)
  have hthreshold : r⁻¹ ^ 2 ≤ (A.limitRadius r)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hinv 2
  have hcanonical : SurgeryCanonicalControl F t x S.setup.epsilon S.setup.C := by
    simpa only [hepsilon, hC] using
      canonical t ht (O.interval_subset ht) x (hthreshold.trans hQ)
  cases hcanonical with
  | neck N hcenter =>
    have h := S.calibration.model_analytics.neck (F.metric t) (F.connection t) N.neck
      (N.epsilon_eq.trans_le heps)
    rw [hcenter] at h
    exact h.mono A.neck_bound
  | cap N _ hconstant hconnection hcore =>
    have h := (N.core_analytic x hcore).mono (hconstant.trans A.cap_bound)
    simpa only [hconnection] using h
  | round N hx =>
    exact (S.calibration.model_analytics.round (F.metric t) (F.connection t)
      S.setup.epsilon N heps x hx).mono A.round_bound
  | component N hx =>
    have hwindow := A.component_window O hr hre ht x hQ
    have hlarge := (A.threshold_bounds hr hre hQ).1
    apply (A.component.estimate S.setup.standard_initial S.constants F hstd
      old.local_constants_eq hC (hepsilon.trans_le heps) t
      ((F.connection t).scalarCurvature x) x rfl hlarge
      (fun s hs => O.interval_subset (hwindow hs))
      (fun s hs => old.pinched s (hwindow hs) (O.interval_subset (hwindow hs)))
      ?_ ?_ (N.mono_constant (by linarith [S.setup.C_pos])) hx).mono A.component_bound
    · intro s hs y hy
      have hsO := hwindow ⟨hs.1, hs.2.le⟩
      simpa only [hC] using canonical s hsO (O.interval_subset hsO) y
        (hthreshold.trans (hQ.trans hy))
    · intro s hs _
      exact (old.delta_le_initial hp s (hwindow hs).1).trans A.delta_le_component

theorem observed {r : ℝ} (hr : 0 < r) (hre : r ≤ S.setup.epsilon)
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) r) :
    SurgeryHighCurvatureAnalyticOn F (surgeryObservationInterval O)
      (A.limitRadius r) S.calibration.analytic_constant := by
  intro t ht _ x hQ
  exact (A.pointwise hp old hr hre canonical t ht x hQ).2

theorem continuation
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    (controls : SurgeryEpochContinuationControls p F O Q R) :
    SurgeryHighCurvatureAnalyticOn F (surgeryObservationInterval O)
      (A.limitRadius R.rNext) S.calibration.analytic_constant := by
  apply A.observed hp old R.r_pos _ controls.canonical
  exact R.r_le_last.trans ((p.r_le_epsilon _).trans_eq
    (congrArg SurgeryControlSetup.epsilon hp.setup_eq))

theorem frontier_scale
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    (controls : SurgeryEpochContinuationControls p F O Q R)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hend : O.H < surgeryEpochStart (p.i + 1)) :
    F.parameters.r O.H = R.rNext ∧
      F.parameters.h O.H = S.setup.selector.h
        (F.parameters.delta O.H * R.rNext) (F.parameters.delta O.H) ∧
      F.parameters.delta O.H * R.rNext < A.limitRadius R.rNext := by
  have hEpoch : O.H ∈ surgeryEpoch p.i := ⟨hstart, hend⟩
  have hr := controls.next_r O.H hEpoch
  refine ⟨hr, ?_, ?_⟩
  · simpa only [hp.setup_eq, hr] using controls.next_h O.H hEpoch
  · apply A.cut_scale_lt_radius old hp R.r_pos _ O.H O.H_pos.le
    exact R.r_le_last.trans ((p.r_le_epsilon _).trans_eq
      (congrArg SurgeryControlSetup.epsilon hp.setup_eq))

end M48AnalyticCalibration

end PoincareConjecture
