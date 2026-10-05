import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyRawFlow
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyRetained

/-!
# Preserving the original flow in the permanent empty continuation

Morgan--Tian Section 17.2, p. 409. The complete extension keeps every old
ordinary transport and both kinds of surgery event, including the actual
retained regions and retention maps. Its domain is all nonnegative time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M51Empty

noncomputable def extension (F : SurgeryFlowData.{u}) {a : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier] : SurgeryFlowExtension F where
  extended := flow F ha
  old_times := F.time_domain_nonnegative
  standard_initial_eq := rfl
  local_constants_eq := rfl
  parameters_eq := rfl
  identify := identify F ha
  metric_pullback := identify_metric_pullback F ha
  old_surgery_times := fun _ _ => Iff.rfl
  ordinary_compatibility := fun p q hpq hJ hfree hJ' _ s t x =>
    identify_ordinary_compatibility F ha p q hpq hJ hfree hJ' s t x
  old_event_reference := fun _ _ _ _ _ => rfl
  old_retained_post := by
    intro T hT _ hOld hNew
    let : Nonempty (slice F a T).carrier := hNew
    exact event_retained_post F ha T hT
  old_retained_pre := by
    intro T hT _ hOld hNew t ht _
    let : Nonempty (slice F a T).carrier := hNew
    exact event_retained_pre F ha T hT t ht
  old_retention := by
    intro T hT _ hOld hNew t ht _ x _
    let : Nonempty (slice F a T).carrier := hNew
    exact event_retention F ha T hT t ht x
  old_vanishing_reference := fun _ _ _ _ _ => rfl

@[simp] theorem extension_time_domain (F : SurgeryFlowData.{u}) {a : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier] :
    (extension F ha).extended.time_domain = Ici 0 := rfl

end PoincareMT.M51Empty
