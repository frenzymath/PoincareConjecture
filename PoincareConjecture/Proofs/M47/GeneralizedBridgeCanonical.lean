import PoincareConjecture.Proofs.M47.GeneralizedBridgeNeck
import PoincareConjecture.Proofs.M47.GeneralizedBridgeCap
import PoincareConjecture.Proofs.M47.GeneralizedBridgeComponent
import PoincareConjecture.Proofs.M47.GeneralizedBridgeRound










set_option autoImplicit false

universe u

namespace PoincareConjecture.M47



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

end PoincareConjecture.M47
