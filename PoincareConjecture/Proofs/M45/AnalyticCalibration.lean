import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Proofs.M32.Calibration

set_option autoImplicit false

universe u

namespace PoincareConjecture.RepairedControlledSchedulesData

noncomputable def recalibrateAnalytic
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    RepairedControlledSchedulesData.{u} := by
  let raw := Classical.choice (S.calibration.horn_selection A hA)
  have hbound : 0 < S.constants.R₀ ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos S.constants.R₀_pos _
  let selected := raw.restrictHeight S.constants.delta₀
    (S.constants.R₀ ^ (-1 / 2 : ℝ)) S.constants.delta₀_pos hbound
  let setup : SurgeryControlSetup S.constants :=
    { S.setup with
      selector := selected.toCommonSurgeryScaleSelector
      selector_delta := fun rho delta _ _ =>
        raw.restrictHeight_le_radius _ _ S.constants.delta₀_pos hbound rho delta }
  exact { S with
    setup := setup
    calibration := { S.calibration with
      analytic_constant := A
      analytic_constant_pos := hA
      horn_selector := selected
      selector_eq := rfl
      selector_initial_bound :=
        raw.restrictHeight_le_bound _ _ S.constants.delta₀_pos hbound _ _ } }

theorem recalibrateAnalytic_constant
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).calibration.analytic_constant = A := rfl

theorem recalibrateAnalytic_constants
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).constants = S.constants := rfl

theorem recalibrateAnalytic_epsilon
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).setup.epsilon = S.setup.epsilon := rfl

theorem recalibrateAnalytic_C
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).setup.C = S.setup.C := rfl

theorem recalibrateAnalytic_kappa0
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).kappa0 = S.kappa0 := rfl

theorem recalibrateAnalytic_Delta0
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).Delta0 = S.Delta0 := rfl

theorem recalibrateAnalytic_standard_initial
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).standard_initial = S.standard_initial := rfl

theorem recalibrateAnalytic_setup_standard_initial
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).setup.standard_initial = S.setup.standard_initial := rfl

theorem recalibrateAnalytic_standard_flow
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).setup.standard_flow = S.setup.standard_flow := rfl

theorem recalibrateAnalytic_cap_persistence
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).cap_persistence = S.cap_persistence := rfl

theorem recalibrateAnalytic_appendixA
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).calibration.appendixA = S.calibration.appendixA := rfl

theorem recalibrateAnalytic_common_epsilon
    (S : RepairedControlledSchedulesData.{u}) (A : ℝ) (hA : 0 < A) :
    (S.recalibrateAnalytic A hA).calibration.common_epsilon =
      S.calibration.common_epsilon := rfl

end PoincareConjecture.RepairedControlledSchedulesData
