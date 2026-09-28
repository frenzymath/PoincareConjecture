import PoincareConjecture.Proofs.M47.SeedM15TestHistory
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_21_ObservedAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem seedM15_path_scalar_lower (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {W : M33RegularHistoryWindow F} (R : M46RegularSpacetimeData W)
    {T tau : ℝ} {x y : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 tau x y)
    (hwindow : Icc (T - tau) T ⊆ R.history.generalized.interval) :
    ∀ s ∈ Icc 0 tau,
      -6 ≤ horizontalScalarCurvature R.geometry.toLGeometry.leafwise (path.curve s) := by
  intro s hs
  have hclock : (path.curve s).1 = T - s := path.curve_time s hs
  have ht : (path.curve s).1 ∈ R.history.generalized.interval := by
    apply hwindow
    rw [hclock]
    constructor <;> linarith [hs.1, hs.2]
  have hp := hpinch (path.curve s).1 (W.time_subset (R.history.interval_eq ▸ ht))
  have hden : 0 < 1 + 4 * (path.curve s).1 := by linarith [hp.1]
  have hfloor : -6 ≤ -6 / (1 + 4 * (path.curve s).1) :=
    (le_div_iff₀ hden).mpr (by nlinarith [hp.1])
  change -6 ≤ horizontalScalarCurvature R.geometry.leafwise
    (⟨(path.curve s).1, (path.curve s).2⟩ : R.history.generalized.point)
  rw [Proofs.M13.originalSlice_scalar R.geometry P.m13 _ (path.curve s).2,
    ← R.history.scalar_pullback _ ht (path.curve s).2]
  exact hfloor.trans (hp.2.1 _ (mem_univ _))

theorem seedM15_path_positiveAction_le (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} (H : SeedM15TestHistory T hT hTF x r)
    (hpinch : SurgeryFlowPinched F) (hceiling : T ≤ surgeryEpochStart (p.i + 1))
    {tau : ℝ} {y : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0 tau
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val y)
    (htau : tau ≤ T - surgeryEpochStart (p.i - 1))
    (hpath : M14BackwardLAction H.spacetime.geometry.toLGeometry path < actionBudget p) :
    (∫ s in 0..tau, Real.sqrt s * pathPositiveDensity path s) ≤ positiveActionBudget p := by
  have hstart : 0 ≤ surgeryEpochStart (p.i - 1) := by unfold surgeryEpochStart; positivity
  have htauTime : tau ≤ T := by linarith
  have hwindow : Icc (T - tau) T ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hscalar := seedM15_path_scalar_lower P hpinch H.spacetime path hwindow
  have hbound := pathPositiveAction_le_action_add P.m12 path (K := 6) (by norm_num)
    (fun s hs => hscalar s ⟨hs.1.le, hs.2.le⟩)
  have htauH : tau ≤ surgeryEpochStart (p.i + 1) := htauTime.trans hceiling
  have hH : 0 ≤ surgeryEpochStart (p.i + 1) := by unfold surgeryEpochStart; positivity
  have hcorrection := mul_le_mul htauH (Real.sqrt_le_sqrt htauH)
    (Real.sqrt_nonneg tau) hH
  unfold positiveActionBudget
  nlinarith

theorem seedM15_path_squareEnergy_le (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} (H : SeedM15TestHistory T hT hTF x r)
    (hpinch : SurgeryFlowPinched F) (hceiling : T ≤ surgeryEpochStart (p.i + 1))
    {tau : ℝ} {y : H.spacetime.geometry.toLGeometry.Point}
    (path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0 tau
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val y)
    (htau : tau ≤ T - surgeryEpochStart (p.i - 1))
    (hpath : M14BackwardLAction H.spacetime.geometry.toLGeometry path < actionBudget p) :
    IntervalIntegrable (M14.pathSquareKinetic path) volume 0 (Real.sqrt tau) ∧
      (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic path s) ≤
        2 * positiveActionBudget p := by
  refine ⟨?_, (pathSquareKinetic_integral_le_positiveAction P.m12 path).trans ?_⟩
  · change IntervalIntegrable (fun s =>
      H.spacetime.geometry.toLGeometry.spacetime.horizontalMetric.inner (path.curve (s ^ 2))
        ((2 * s) • path.horizontal_velocity (s ^ 2))
        ((2 * s) • path.horizontal_velocity (s ^ 2))) volume 0 (Real.sqrt tau)
    simpa only [Real.sqrt_zero] using M14.squarePath_kinetic_intervalIntegrable path P.m12
  · exact mul_le_mul_of_nonneg_left
      (seedM15_path_positiveAction_le P p H hpinch hceiling path htau hpath) (by norm_num)

end PoincareConjecture.M47
