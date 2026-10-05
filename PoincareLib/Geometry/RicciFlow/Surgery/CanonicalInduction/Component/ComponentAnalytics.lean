import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Scalar.ScalarPersistence
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Derivative
import PoincareLib.Geometry.RicciFlow.MetricComparison.Curvature
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.ModelAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Prefix.Initial

/-!
# Component coefficient supply and pre-flow calibration

The producer uses only the displayed M04 services and M47's existing
admission. Calibration chooses the component cutoff and a common analytic
coefficient before any prefix or flow, retaining the actual standard model.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

theorem m47ComponentAnalyticPredecessors_from_M04 :
    M47ComponentAnalyticPredecessors.{u} := {
  toM47ScalarPersistencePredecessors := m47ScalarPersistencePredecessors_from_M04
  local_derivative_estimates := @local_curvatureDerivative_bound 3
  metric_comparison := @RicciFlow.metric_comparison_of_curvature_bound 3
}

/-- The selected M47 output at the actual geometric constant. -/
theorem m47ComponentAnalytics_from_predecessors
    (T : RepairedCanonicalInductionTheory.{u})
    (P : M47ComponentAnalyticPredecessors.{u}) (C : ℝ) (hC : 1 ≤ C) :
    Nonempty (M47ComponentAnalyticBounds.{u} C) :=
  T.component_analytics P C hC

/-- Both earlier proof services are supplied; no raw-flow hypothesis is added. -/
theorem m47ComponentAnalyticsFromMilestones (C : ℝ) (hC : 1 ≤ C) :
    Nonempty (M47ComponentAnalyticBounds.{u} C) :=
  m47ComponentAnalytics_from_predecessors m47CanonicalInductionFromMilestones
    m47ComponentAnalyticPredecessors_from_M04 C hC

namespace RepairedControlledSchedulesData

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C)

/-- Neither the previous height selector nor a flow enters this coefficient. -/
noncomputable def componentAnalyticConstant : ℝ :=
  2 * max S.modelAnalyticBound B.constant

theorem componentAnalyticConstant_pos : 0 < S.componentAnalyticConstant B :=
  mul_pos (by norm_num) (S.modelAnalyticBound_pos.trans_le (le_max_left _ _))

theorem componentAnalyticConstant_half :
    S.componentAnalyticConstant B / 2 = max S.modelAnalyticBound B.constant := by
  unfold componentAnalyticConstant
  ring

theorem model_le_componentAnalyticConstant_half :
    S.modelAnalyticBound ≤ S.componentAnalyticConstant B / 2 := by
  rw [S.componentAnalyticConstant_half B]
  exact le_max_left _ _

theorem component_le_componentAnalyticConstant_half :
    B.constant ≤ S.componentAnalyticConstant B / 2 := by
  rw [S.componentAnalyticConstant_half B]
  exact le_max_right _ _

/-- Restrict the actual initial cutoff, then reselect the height, before flows. -/
noncomputable def calibrateComponentAnalytics : RepairedControlledSchedulesData.{u} :=
  (S.restrictDelta (B.delta S.setup.standard_initial S.constants)
    (B.delta_pos _ _)).recalibrateAnalytic
      (S.componentAnalyticConstant B) (S.componentAnalyticConstant_pos B)

theorem calibrateComponentAnalytics_constant :
    (S.calibrateComponentAnalytics B).calibration.analytic_constant =
      S.componentAnalyticConstant B := rfl

theorem calibrateComponentAnalytics_epsilon :
    (S.calibrateComponentAnalytics B).setup.epsilon = S.setup.epsilon := rfl

theorem calibrateComponentAnalytics_C :
    (S.calibrateComponentAnalytics B).setup.C = S.setup.C := rfl

theorem calibrateComponentAnalytics_kappa0 :
    (S.calibrateComponentAnalytics B).kappa0 = S.kappa0 := rfl

theorem calibrateComponentAnalytics_Delta0 :
    (S.calibrateComponentAnalytics B).Delta0 =
      min S.Delta0 (B.delta S.setup.standard_initial S.constants) := rfl

theorem calibrateComponentAnalytics_cutoff :
    (S.calibrateComponentAnalytics B).Delta0 ≤
      B.delta S.setup.standard_initial S.constants := min_le_right _ _

theorem calibrateComponentAnalytics_standard_flow :
    (S.calibrateComponentAnalytics B).setup.standard_flow =
      S.setup.standard_flow := rfl

theorem calibrateComponentAnalytics_cap_persistence :
    (S.calibrateComponentAnalytics B).cap_persistence = S.cap_persistence := rfl

/-- The selected component estimate keeps the coefficient's factor-two margin. -/
theorem componentAnalyticEstimate (F : SurgeryFlowData.{u})
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    (hEpsilon : F.parameters.epsilon ≤ 1 / 200)
    (t Q : ℝ) (x : (F.slice t).carrier)
    (hQ : (F.connection t).scalarCurvature x = Q)
    (hLarge : B.curvature_threshold ≤ Q)
    (hDomain : Set.Icc (t - B.duration / Q) t ⊆ F.time_domain)
    (hPinched : ∀ s ∈ Set.Icc (t - B.duration / Q) t,
      SurgeryPinchedAt (F.connection s) s)
    (hCanonical : ∀ s ∈ Set.Ico (t - B.duration / Q) t, ∀ y : (F.slice s).carrier,
      Q ≤ (F.connection s).scalarCurvature y →
        SurgeryCanonicalControl F s y F.parameters.epsilon S.setup.C)
    (hDelta : ∀ T ∈ Set.Icc (t - B.duration / Q) t, T ∈ F.surgery_times →
      F.parameters.delta T ≤ (S.calibrateComponentAnalytics B).Delta0)
    (N : SingularCComponent (F.metric t) (F.connection t) (2 * S.setup.C))
    (hx : x ∈ N.carrier) :
    M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x
      ((S.calibrateComponentAnalytics B).calibration.analytic_constant / 2) := by
  apply (B.estimate S.setup.standard_initial S.constants F hInitial hConstants hC
    hEpsilon t Q x hQ hLarge hDomain hPinched hCanonical
    (fun T hT hS => (hDelta T hT hS).trans (S.calibrateComponentAnalytics_cutoff B))
    N hx).mono
  exact S.component_le_componentAnalyticConstant_half B

end RepairedControlledSchedulesData

end PoincareMT
