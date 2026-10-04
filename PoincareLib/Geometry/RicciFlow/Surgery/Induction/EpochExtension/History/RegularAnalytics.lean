import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ScalarGradientTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.LimitRadius
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ObservedAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularSliceTransport

/-!
# Apply the actual scalar estimates to the retained M48 history

Every metric, connection and clock belongs to the one selected history.
The M12 box identity uses its literal box-flow connection; it composes with
the supplied M13 slice identity and M33 scalar pullback. Sources:
Morgan--Tian Assumptions 11.18, p. 279, and Section 17.2, pp. 409-410.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

theorem M48Predecessors.regular_box_scalar (P : M48Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
    (R : M48RegularSpacetimeData L) (b : R.history.generalized.box_index)
    (t : ℝ) (ht : t ∈ (R.history.generalized.box b).interval)
    (x : (R.history.generalized.box b).carrier.carrier) :
    ((R.history.generalized.box b).flow.connection t).scalarCurvature x =
      (F.connection t).scalarCurvature
        (R.history.history.forward t (m33BoxIntervalSubset _ b ht)
          ((R.history.generalized.box b).forward t ht x)) := by
  let G := R.history.generalized
  let V := R.geometry.realization
  let gauges := P.m12.gauges G.point Sigma.fst (EpochExtension.Spacetime.flowInterval G)
    V.spacetime V.slices V.timeIntervals V.gaugeCover R.geometry.leafwise
  let calculus := gauges.moving_calculus (G.box b).carrier.carrier
    (EpochExtension.Spacetime.boxInterval G b)
    (EpochExtension.Spacetime.originalBoxCylinder G V b).toMovingSpacetimeGauge
    (EpochExtension.Spacetime.originalBoxMetric G V b).toMovingSpacetimeGaugeGeometry
    (G.box b).flow.connection
  exact (calculus.scalar_eq ⟨t, ht⟩ x).trans
    (P.regular_scalar R t (m33BoxIntervalSubset G b ht) ((G.box b).forward t ht x))

namespace M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
  {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
  {O : SurgeryObservation F} (hp : S.SeedCompatible p)
  (old : SurgeryPrefixControls p F O)
  {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
  (controls : SurgeryEpochContinuationControls p F O Q N)
  {L : RepairedPreterminalSlab F O.H} (R : M48RegularSpacetimeData L)

include hp old controls in
/-- M31's directional bound on the actual selected history, without an analytic premise. -/
theorem regular_gradient (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (x : (R.history.generalized.slice t).carrier)
    (hQ : (A.historyRadius N.rNext)⁻¹ ^ 2 ≤
      (R.history.generalized.connection t).scalarCurvature x)
    (v : TangentSpace (𝓡 3) x) (hv : (R.history.generalized.metric t).inner x v v = 1) :
    |mvfderiv (𝓡 3) (R.history.generalized.connection t).scalarCurvature x v| ≤
      S.calibration.analytic_constant *
        (R.history.generalized.connection t).scalarCurvature x ^ (3 / 2 : ℝ) := by
  apply R.history.scalar_gradient _ (A.continuation hp old controls) t ht x
    ((A.history_threshold N.r_pos).le.trans hQ) v hv
  intro s hs
  exact (show s ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ hs)

include old in
theorem regular_pinched (t : ℝ) (ht : t ∈ R.history.generalized.interval) :
    SurgeryPinchedAt (R.history.generalized.connection t) t := by
  have htO : t ∈ surgeryObservationInterval O :=
    (show t ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ ht)
  exact R.history.pinched_at t ht (old.pinched t htO (O.interval_subset htO))

include old in
theorem regular_scalar_lower_bound (t : ℝ) (ht : t ∈ R.history.generalized.interval)
    (x : (R.history.generalized.slice t).carrier) :
    -6 ≤ (R.history.generalized.connection t).scalarCurvature x := by
  have htO : t ∈ surgeryObservationInterval O :=
    (show t ∈ L.regularHistoryWindow.interval from R.history.interval_eq ▸ ht)
  exact R.history.scalar_lower_bound t ht (old.pinched t htO (O.interval_subset htO)) x

include hp old controls in
theorem frontier_history_scale
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hend : O.H < surgeryEpochStart (p.i + 1)) :
    F.parameters.r O.H = N.rNext ∧
      F.parameters.h O.H = S.setup.selector.h
        (F.parameters.delta O.H * N.rNext) (F.parameters.delta O.H) ∧
      F.parameters.delta O.H * N.rNext < A.historyRadius N.rNext := by
  have h := A.frontier_scale hp old controls hstart hend
  refine ⟨h.1, h.2.1, A.cut_scale_lt_historyRadius old hp N.r_pos ?_ O.H O.H_pos.le⟩
  exact N.r_le_last.trans ((p.r_le_epsilon _).trans_eq
    (congrArg SurgeryControlSetup.epsilon hp.setup_eq))

end M48AnalyticCalibration

end PoincareMT
