import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Definitions.M47ComponentAnalytics

set_option autoImplicit false

universe u

namespace PoincareConjecture

structure M48AnalyticCalibration (S : RepairedControlledSchedulesData.{u}) where
  component : M47ComponentAnalyticBounds.{u} S.setup.C
  delta_le_component :
    S.Delta0 ≤ component.delta S.setup.standard_initial S.constants
  delta_radius :
    2 * S.Delta0 * S.setup.epsilon ≤ (component.curvature_threshold + 1)⁻¹
  neck_bound :
    S.calibration.model_analytics.neck_constant ≤ S.calibration.analytic_constant
  round_bound :
    S.calibration.model_analytics.round_constant ≤ S.calibration.analytic_constant
  cap_bound : S.setup.C ≤ S.calibration.analytic_constant
  component_bound : component.constant ≤ S.calibration.analytic_constant

end PoincareConjecture
