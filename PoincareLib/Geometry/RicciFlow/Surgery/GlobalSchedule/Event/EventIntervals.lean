import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossData

/-!
# Actual pre-surgery intervals in the raw flow domain

These two M49 input predicates follow from Definition 15.5's actual clock
and event data. The separate zero-cap component assertion is not a domain
consequence and is not proved here.
-/

set_option autoImplicit false

universe u

namespace PoincareMT
namespace SurgeryFlowData

theorem nonemptyEventPreInterval (F : SurgeryFlowData.{u}) :
    RepairedNonemptyEventPreInterval F := by
  intro T hT _ t ht
  exact F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
    ⟨(F.event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

theorem vanishingEventPreInterval (F : SurgeryFlowData.{u}) :
    RepairedVanishingEventPreInterval F := by
  intro T hT _ t ht
  exact F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
    ⟨(F.vanishing_event T hT).tMinus_nonnegative.trans ht.1, ht.2.le⟩

end SurgeryFlowData
end PoincareMT
