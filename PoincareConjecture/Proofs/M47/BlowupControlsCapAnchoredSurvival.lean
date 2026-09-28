import PoincareConjecture.Proofs.M47.BlowupControlsCapAnchoredNecks
import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47

theorem cap_not_disappears_of_anchored_carrier
    {F : SurgeryFlowData.{u}} {origin scale tau d : ℝ}
    {N E : EpsilonNeck (F.metric origin)} {b : ℝ}
    {V : Set (F.slice origin).carrier}
    (hcarrier : E.carrier = N.region b N.epsilon⁻¹)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale
      (Ico 0 tau) E.carrier)
    (f : SurgeryFlowCylinder F (F.slice origin) origin scale
      (Icc 0 d) V)
    (htau : 0 < tau) (htaud : tau < d)
    (y : (F.slice origin).carrier)
    (hyregion : y ∈ N.region b N.epsilon⁻¹) (hyV : y ∈ V)
    (hinitial : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x) :
    ¬ SurgeryBallDisappearsAt F e (origin + tau / scale) := by
  have hyE : y ∈ E.carrier := by
    rw [hcarrier]
    exact hyregion
  exact cap_not_disappears_of_surviving_cylinder e f htau htaud y hyE hyV hinitial

end PoincareConjecture.M47
