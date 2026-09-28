import PoincareConjecture.Proofs.M47.BlowupControlsFirstFailure
import PoincareConjecture.Proofs.M47.BlowupControlsCylinderBound

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

theorem first_failure_cylinder_analytic_estimate
    (h04 : RicciFlowCurvatureTheory.{u}) {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier}
    (e : GeneralizedFlowCylinder H.generalized Z base Q (Icc (-T) 0) U)
    {x : Z.carrier} {L : ℝ} (hL : 1 ≤ L) (s : ℝ) (hs : s ∈ Ioo (-T) 0)
    (hHigh : L < normalizedCylinderScalar e x s) :
    let q := e.pointMap s (Ioo_subset_Icc_self hs) x
    M45PointwiseAnalyticEstimate (H.generalized.metric q.1)
      (H.generalized.connection q.1) q.2 (blowupAnalyticConstant S B) := by
  classical
  let q := e.pointMap s (Ioo_subset_Icc_self hs) x
  have ht : q.1 ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff q.1).mp ⟨q.2⟩
  have hTime : q.1 ∈ Ico (base - T / Q) base := by
    have hLower := div_le_div_of_nonneg_right hs.1.le e.scale_pos.le
    have hUpper : s / Q < 0 := div_neg_of_neg_of_pos hs.2 e.scale_pos
    change base - T / Q ≤ base + s / Q ∧ base + s / Q < base
    rw [neg_div] at hLower
    constructor <;> linarith
  have hScalar : Q ≤ H.generalized.scalar q := by
    have hValue : normalizedCylinderScalar e x s = H.generalized.scalar q / Q := by
      simp only [normalizedCylinderScalar, dif_pos (Ioo_subset_Icc_self hs), q]
    rw [hValue] at hHigh
    simpa only [one_mul] using (le_div_iff₀ e.scale_pos).mp (hL.trans hHigh.le)
  exact first_failure_generalized_analytic_estimate S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap h04 H ht hTime q.2 hScalar

theorem first_failure_cylinder_scalar_bound
    (h04 : RicciFlowCurvatureTheory.{u}) {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier}
    (e : GeneralizedFlowCylinder H.generalized Z base Q (Icc (-T) 0) U)
    {x : Z.carrier} (hx : x ∈ U) {L : ℝ} (hL : 1 ≤ L)
    (hTerminal : normalizedCylinderScalar e x 0 ≤ L)
    (hShort : blowupAnalyticConstant S B * L * T ≤ 1 / 4) :
    ∀ s ∈ Icc (-T) 0, normalizedCylinderScalar e x s ≤ 4 * L / 3 := by
  apply normalizedCylinderScalar_le h04 e hx (neg_nonpos.mpr hT)
    (blowupAnalyticConstant_pos S B).le (zero_lt_one.trans_le hL) hTerminal ?_ (by
      simpa only [neg_neg] using hShort)
  exact first_failure_cylinder_analytic_estimate S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap h04 H e hL

theorem first_failure_cylinder_curvature_bounds
    (P : M46Predecessors.{u}) {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {Z : GeneralizedSliceCarrier.{u}} {U : Set Z.carrier}
    (e : GeneralizedFlowCylinder H.generalized Z base Q (Icc (-T) 0) U)
    {x : Z.carrier} (hx : x ∈ U) {L : ℝ} (hL : 1 ≤ L)
    (hTerminal : normalizedCylinderScalar e x 0 ≤ L)
    (hShort : blowupAnalyticConstant S B * L * T ≤ 1 / 4) {eta : ℝ} (heta : 0 < eta)
    (hPinchingScale : blowupPinchingThreshold (4 * L / 3) eta ≤ Q) :
    ∀ s (hs : s ∈ Icc (-T) 0),
      let q := e.pointMap s hs x
      |H.generalized.curvatureNorm q| ≤ (13 * max (4 * L / 3) 1) * Q ∧
        (H.generalized.connection q.1).negativeCurvaturePart q.2 ≤ eta * Q := by
  have hGeneralized := regular_history_hamiltonIvey H
    (fun t ht => hPinched t (W.time_subset ht))
  apply normalizedCylinder_curvature_bounds P hGeneralized e hx (neg_nonpos.mpr hT)
    (blowupAnalyticConstant_pos S B).le (zero_lt_one.trans_le hL) hTerminal ?_ (by
      simpa only [neg_neg] using hShort) heta hPinchingScale
  exact first_failure_cylinder_analytic_estimate S B p O hInitial hConstants hC
    hBase hT hScale hLarge hThreshold hPinched hEarlier hOverlap P.m04 H e hL

end PoincareConjecture.M47
