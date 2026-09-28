import PoincareConjecture.Definitions.M49VolumeLoss

set_option autoImplicit false

universe u

namespace PoincareConjecture
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
end PoincareConjecture
