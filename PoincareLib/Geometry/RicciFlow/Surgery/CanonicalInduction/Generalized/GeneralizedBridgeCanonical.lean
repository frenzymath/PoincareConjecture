import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeNeck
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeCap
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeComponent
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Generalized.GeneralizedBridgeRound

/-!
# Full canonical control on the actual regular generalized slice

Every alternative is a genuine transported geometric certificate. The
strong neck retains its full earlier cylinder; the three static carriers
use the actual global slice isometry at a nonsurgery time.
Source: Morgan--Tian Definition 9.78 and Proposition 14.12.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M47

/-- Actual surgery canonical control transports at a regular included
time with its identical epsilon and C. -/
theorem regular_history_canonical_control
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)
    (hregular : t ∉ F.surgery_times) {epsilon C : ℝ}
    (x : (H.generalized.slice t).carrier)
    (hcanonical : SurgeryCanonicalControl F t (H.history.forward t ht x) epsilon C) :
    Nonempty (GeneralizedCanonicalControl (F := H.generalized) t x epsilon C) := by
  cases hcanonical with
  | neck N hcenter => exact regular_history_neck_control H ht x N hcenter
  | cap N he hC _ hx => exact regular_history_cap_control H ht hregular x N he hC hx
  | component N hx => exact regular_history_component_control H ht hregular x N hx
  | round N hx => exact regular_history_round_control H ht hregular x N hx

end PoincareMT.M47
