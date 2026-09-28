import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_1_BarrierParameters
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_PositiveSquareEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46



theorem actionBudget_large {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T : ℝ}
    (hT : T ≤ surgeryEpochStart (p.i + 1)) :
    3 * Real.sqrt (T - surgeryEpochStart (p.i - 1)) < actionBudget p := by
  have hH : 0 < surgeryEpochStart (p.i + 1) := by unfold surgeryEpochStart; positivity
  have hstart : 0 ≤ surgeryEpochStart (p.i - 1) := by unfold surgeryEpochStart; positivity
  have hroot : 0 < Real.sqrt (surgeryEpochStart (p.i + 1)) := Real.sqrt_pos.mpr hH
  have hmono := Real.sqrt_le_sqrt (show T - surgeryEpochStart (p.i - 1) ≤
    surgeryEpochStart (p.i + 1) by linarith)
  unfold actionBudget
  nlinarith [mul_nonneg hH.le hroot.le]




theorem observed_path_positiveAction_le (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hnext : SurgeryObservationIsNextEpoch p O)
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D)
    {tau : ℝ} {y : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry D.time 0 tau
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val y)
    (htau : tau ≤ D.time - surgeryEpochStart (p.i - 1))
    (hpath : M14BackwardLAction H.spacetime.geometry.toLGeometry path < actionBudget p) :
    (∫ s in 0..tau, Real.sqrt s * pathPositiveDensity path s) ≤ positiveActionBudget p := by
  have hstart : 0 ≤ surgeryEpochStart (p.i - 1) := by unfold surgeryEpochStart; positivity
  have htauTime : tau ≤ D.time := by linarith
  have hwindow : Icc (D.time - tau) D.time ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hscalar := regular_history_path_scalar_lower P old H.spacetime path
    D.time_mem htauTime hwindow
  have hbound := pathPositiveAction_le_action_add P.m12 path (K := 6) (by norm_num)
    (fun s hs => hscalar s ⟨hs.1.le, hs.2.le⟩)
  have htauH : tau ≤ surgeryEpochStart (p.i + 1) :=
    htauTime.trans (D.time_mem.2.le.trans hnext.2)
  have hH : 0 ≤ surgeryEpochStart (p.i + 1) := by unfold surgeryEpochStart; positivity
  have hcorrection := mul_le_mul htauH (Real.sqrt_le_sqrt htauH)
    (Real.sqrt_nonneg tau) hH
  unfold positiveActionBudget
  nlinarith




theorem observed_path_squareEnergy_le (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hnext : SurgeryObservationIsNextEpoch p O)
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D)
    {tau : ℝ} {y : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry D.time 0 tau
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val y)
    (htau : tau ≤ D.time - surgeryEpochStart (p.i - 1))
    (hpath : M14BackwardLAction H.spacetime.geometry.toLGeometry path < actionBudget p) :
    IntervalIntegrable (M14.pathSquareKinetic path) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic path s) ≤
        2 * positiveActionBudget p := by
  refine ⟨?_, (pathSquareKinetic_integral_le_positiveAction P.m12 path).trans ?_⟩
  · change IntervalIntegrable (fun s =>
      H.spacetime.geometry.toLGeometry.spacetime.horizontalMetric.inner (path.curve (s ^ 2))
        ((2 * s) • path.horizontal_velocity (s ^ 2))
        ((2 * s) • path.horizontal_velocity (s ^ 2))) volume 0 (Real.sqrt tau)
    simpa only [Real.sqrt_zero] using
      M14.squarePath_kinetic_intervalIntegrable path P.m12
  · exact mul_le_mul_of_nonneg_left
      (observed_path_positiveAction_le P p old hnext H path htau hpath) (by norm_num)

end PoincareConjecture.Proofs.M46
