import PoincareLib.Geometry.RicciFlow.Surgery.Control.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.ComponentBounds

/-!
Adapted from Mapher `PoincareMT/Definitions/M48AnalyticCalibration.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# Analytic calibration before the M48 singular step

The actual M47 component estimate and the M45 model estimates must share a
coefficient with the selected M32 height. Choose these data before the
induction packages, prefixes and flows. For a geometric radius r, the M31
application uses min r (component.curvature_threshold + 1)⁻¹.
Sources: Morgan--Tian Assumptions 11.18, Theorem 11.31 and Section 17.2,
pp. 276--290 and 409--410. See the September 19 calibration-boundary review.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Earlier theorem data and numerical calibration, with no flow or
continuation conclusion as a premise. The component field retains its actual
estimate, rather than just the name or size of an analytic constant. -/
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

end PoincareMT
