import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochTheory
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Component.ComponentAnalytics

/-!
# Constructing the calibration before selecting induction data

Restrict the cutoff and then select M32's height using the same coefficient
as the actual M45/M47 estimates. These checked constructions supply M48's
calibration premise; they do not construct a regular history or a flow.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

namespace RepairedControlledSchedulesData

variable (S : RepairedControlledSchedulesData.{u})
  (B : M47ComponentAnalyticBounds.{u} S.setup.C)

noncomputable def epochAnalyticRadius : ℝ := (B.curvature_threshold + 1)⁻¹

theorem epochAnalyticRadius_pos : 0 < S.epochAnalyticRadius B := by
  apply inv_pos.mpr
  linarith [B.one_le_curvature_threshold]

noncomputable def epochAnalyticCutoff : ℝ :=
  min (B.delta S.setup.standard_initial S.constants)
    (S.epochAnalyticRadius B / (2 * S.setup.epsilon))

theorem epochAnalyticCutoff_pos : 0 < S.epochAnalyticCutoff B :=
  lt_min (B.delta_pos _ _) (div_pos (S.epochAnalyticRadius_pos B)
    (mul_pos (by norm_num) S.setup.epsilon_pos))

/-- This choice precedes N, C, the finite prefix and every surgery flow. -/
noncomputable def calibrateForEpoch : RepairedControlledSchedulesData.{u} :=
  (S.restrictDelta (S.epochAnalyticCutoff B) (S.epochAnalyticCutoff_pos B)).recalibrateAnalytic
    (S.componentAnalyticConstant B) (S.componentAnalyticConstant_pos B)

/-- The chosen setup has the actual component service and all required
coefficient/cutoff bounds. No new geometric estimate is admitted here. -/
noncomputable def epochCalibration : M48AnalyticCalibration (S.calibrateForEpoch B) := by
  have hA : S.modelAnalyticBound ≤ S.componentAnalyticConstant B := by
    have hhalf := S.model_le_componentAnalyticConstant_half B
    have hpos := S.componentAnalyticConstant_pos B
    linarith
  have hC : S.setup.C ≤ S.componentAnalyticConstant B := by
    rw [S.calibration.setup_C_eq]
    apply max_le
    · exact S.kappa_le_modelAnalyticBound.trans hA
    · have hstandard := S.standard_le_modelAnalyticBound
      have hone := S.one_le_modelAnalyticBound
      have hhalf := S.model_le_componentAnalyticConstant_half B
      linarith
  refine {
    component := B
    delta_le_component := ?_
    delta_radius := ?_
    neck_bound := S.neck_le_modelAnalyticBound.trans hA
    round_bound := S.round_le_modelAnalyticBound.trans hA
    cap_bound := hC
    component_bound := ?_
  }
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · have hcut : min S.Delta0 (S.epochAnalyticCutoff B) ≤
        S.epochAnalyticRadius B / (2 * S.setup.epsilon) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      S.setup.epsilon_pos)).mp hcut
    change 2 * min S.Delta0 (S.epochAnalyticCutoff B) * S.setup.epsilon ≤
      S.epochAnalyticRadius B
    nlinarith
  · have hhalf := S.component_le_componentAnalyticConstant_half B
    have hpos := S.componentAnalyticConstant_pos B
    change B.constant ≤ S.componentAnalyticConstant B
    linarith

end RepairedControlledSchedulesData

/-- A later volume-cutoff restriction preserves this calibration. Concrete
induction packages must still be selected for the final restricted setup. -/
noncomputable def M48AnalyticCalibration.restrictDelta
    {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
    (d : ℝ) (hd : 0 < d) : M48AnalyticCalibration (S.restrictDelta d hd) where
  component := A.component
  delta_le_component := (min_le_left _ _).trans A.delta_le_component
  delta_radius := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_left S.Delta0 d) (by norm_num : (0 : ℝ) ≤ 2))
      S.setup.epsilon_pos.le
    exact h.trans A.delta_radius
  neck_bound := A.neck_bound
  round_bound := A.round_bound
  cap_bound := A.cap_bound
  component_bound := A.component_bound

/-- Apply the public step to the setup constructed from the actual earlier
component service. N and C are indexed by that final setup. -/
theorem RepairedEpochExtensionTheory.calibrated
    (E : RepairedEpochExtensionTheory.{u}) (P : M48Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData (S.calibrateForEpoch B))
    (C : RepairedCanonicalInductionData (S.calibrateForEpoch B) N) :
    Nonempty (RepairedEpochExtensionData (S.calibrateForEpoch B) N C) :=
  E.one_step P (S.calibrateForEpoch B) (S.epochCalibration B) N C

/-- Specialize the actual curvature theory retained by the supplied M32
service. No globally reselected predecessor theorem is used. -/
theorem M48Predecessors.componentAnalyticInputs (P : M48Predecessors.{u}) :
    M47ComponentAnalyticPredecessors.{u} := {
  tensor_calculus := P.m32.providers.m04.tensor_calculus 3
  scalar_regular := P.m32.providers.m04.scalar_regular 3
  scalar_evolution := P.m32.providers.m04.scalar_evolution 3
  local_derivative_estimates := P.m32.providers.m04.local_derivative_estimates 3
  metric_comparison := P.m32.providers.m04.metric_comparison 3
}

/-- The given predecessor services supply B, then induction packages for the
final setup after the extra positive cutoff (for example M49's volume bound).
The selector and seeds are fixed before any prefix or flow is quantified. -/
theorem RepairedEpochExtensionTheory.from_calibrated_predecessors
    (E : RepairedEpochExtensionTheory.{u}) (P : M48Predecessors.{u})
    (G46 : RepairedNoncollapseInductionTheory.{u})
    (G47 : RepairedCanonicalInductionTheory.{u})
    (S : RepairedControlledSchedulesData.{u}) (d : ℝ) (hd : 0 < d) :
    ∃ B : M47ComponentAnalyticBounds.{u} S.setup.C,
      ∃ N : RepairedNoncollapseInductionData
          ((S.calibrateForEpoch B).restrictDelta d hd),
        ∃ C : RepairedCanonicalInductionData
            ((S.calibrateForEpoch B).restrictDelta d hd) N,
          Nonempty (RepairedEpochExtensionData
            ((S.calibrateForEpoch B).restrictDelta d hd) N C) := by
  obtain ⟨B⟩ := G47.component_analytics P.componentAnalyticInputs S.setup.C S.setup.C_large
  let finalSetup := (S.calibrateForEpoch B).restrictDelta d hd
  obtain ⟨N⟩ := G46.induction finalSetup
  obtain ⟨C⟩ := G47.induction finalSetup N
  exact ⟨B, N, C, E.one_step P finalSetup
    ((S.epochCalibration B).restrictDelta d hd) N C⟩

end PoincareMT
