import PoincareConjecture.Proofs.M47.BlowupControlsWindow
import PoincareConjecture.Proofs.M47.BlowupControlsAnalytics
import PoincareConjecture.Proofs.M47.BlowupControlsDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C)
  (p : SurgeryParameterPrefix S.constants)
  {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
  (hInitial : F.standard_initial = S.setup.standard_initial)
  (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
  {base Q T r : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
  (hT : 0 ≤ T) (hScale : 64 * (T + 1) ≤ Q)
  (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
  (hPinched : SurgeryFlowPinched F)
  (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
  (hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
    F.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants)

include hInitial hConstants hC hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap

theorem first_failure_physical_analytic_estimate
    {s : ℝ} (hs : s ∈ Ico (base - T / Q) base) (x : (F.slice s).carrier)
    (hScalar : Q ≤ (F.connection s).scalarCurvature x) :
    M45PointwiseAnalyticEstimate (F.metric s) (F.connection s) x
      (blowupAnalyticConstant S B) := by
  let R := (F.connection s).scalarCurvature x
  have hQpos : 0 < Q := by linarith
  have hRpos : 0 < R := hQpos.trans_le hScalar
  have hWindow := blowup_analytic_window_subset_overlap p hBase hT hScale hScalar
    B.duration_le_one hs
  have hDomain : Icc (s - B.duration / R) s ⊆ F.time_domain :=
    fun _ hu => O.interval_subset (hWindow hu).1
  have hsWindow : s ∈ Icc (s - B.duration / R) s :=
    ⟨sub_le_self _ (div_nonneg B.duration_pos.le hRpos.le), le_rfl⟩
  have hCanonical := hEarlier s ⟨(hWindow hsWindow).1, hs.2⟩ (hDomain hsWindow) x
    (hThreshold.trans hScalar)
  rw [hC] at hCanonical
  apply canonical_blowup_analytic_estimate S B F hInitial hConstants hC s R x rfl
    (hLarge.trans hScalar) hDomain (fun u hu => hPinched u (hDomain hu)) ?_
    (fun u hu _ => hOverlap u (hWindow hu)) F.parameters.epsilon_le
    (by linarith [S.setup.C_pos]) hCanonical
  intro u hu y hy
  have huWindow : u ∈ Icc (s - B.duration / R) s := Ico_subset_Icc_self hu
  have h := hEarlier u ⟨(hWindow huWindow).1, hu.2.trans hs.2⟩ (hDomain huWindow) y
    ((hThreshold.trans hScalar).trans hy)
  simpa only [hC] using h

theorem first_failure_generalized_analytic_estimate
    (h04 : RicciFlowCurvatureTheory.{u}) {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {s : ℝ} (ht : s ∈ H.generalized.interval)
    (hs : s ∈ Ico (base - T / Q) base) (x : (H.generalized.slice s).carrier)
    (hScalar : Q ≤ H.generalized.scalar ⟨s, x⟩) :
    M45PointwiseAnalyticEstimate (H.generalized.metric s) (H.generalized.connection s) x
      (blowupAnalyticConstant S B) := by
  apply regular_history_pointwise_analytic_estimate h04 H ht
  apply first_failure_physical_analytic_estimate S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap hs
  simpa only [GeneralizedRicciFlowData.scalar, H.scalar_pullback s ht] using hScalar

end PoincareConjecture.M47
