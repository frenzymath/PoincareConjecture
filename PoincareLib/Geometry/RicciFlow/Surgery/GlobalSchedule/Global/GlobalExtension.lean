import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Global.GlobalRawFlow
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Global.GlobalEventLedger

/-!
# Every completed stage extends into the global flow

Morgan--Tian Section 17.2, pp. 409-411, and global assembly contract steps
3-7. The representative maps preserve the whole old domain, actual ordinary
transports, and the full retained-region ledger. Composing the retained
initial extension then extends the original input flow itself.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : Nat}
  (Q : CompletedStageChain S N C F0 k)
  (m13 : GeneralizedParabolicRescalingTheory.{u} 3)

/-- The actual global extension of each completed finite stage.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def globalExtension (n : Nat) : SurgeryFlowExtension (Q.flow n) where
  extended := Q.globalFlow m13
  old_times := (Q.flow n).time_domain_nonnegative
  standard_initial_eq := (Q.standard_initial_eq n).symm
  local_constants_eq := (Q.local_constants_eq n).symm
  parameters_eq := (Q.parameters_eq n).symm
  identify := Q.globalIdentify n
  metric_pullback := Q.globalIdentify_metric n
  old_surgery_times := Q.global_surgery_iff n
  ordinary_compatibility := by
    intro a b hab hJ hfree hJ' hfree' s t x
    exact Q.globalSlab_compare a b hab hJ' hfree' n a b hab hJ hfree
      s.1 t.1 s.2 t.2 s.2 t.2 x
  old_event_reference := by
    intro T hT _ hne hT'
    let : Nonempty (Q.globalSlice T).carrier := hne
    exact Q.globalEvent_old_reference n T hT hT'
  old_retained_post := by
    intro T hT hT' _ hne
    let : Nonempty (Q.globalSlice T).carrier := hne
    exact Q.globalEvent_old_retained_post n T hT hT'
  old_retained_pre := by
    intro T hT hT' _ hne t ht ht'
    let : Nonempty (Q.globalSlice T).carrier := hne
    exact Q.globalEvent_old_retained_pre n T hT hT' t ht ht'
  old_retention := by
    intro T hT hT' _ hne t ht ht' x hx
    let : Nonempty (Q.globalSlice T).carrier := hne
    exact Q.globalEvent_old_retention n T hT hT' t ht ht' x hx
  old_vanishing_reference := by
    intro T hT _ he hT'
    let : IsEmpty (Q.globalSlice T).carrier := he
    exact Q.globalVanishingEvent_old_reference m13 n T hT hT'

/-- Every stage extension has the same literal global target.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalExtension_extended (n : Nat) :
    (Q.globalExtension m13 n).extended = Q.globalFlow m13 := rfl

/-- Its old-slice maps are precisely the representative maps already checked.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem globalExtension_identify (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    (Q.globalExtension m13 n).identify t ht = Q.globalIdentify n t ht := rfl

/-- Extend the original input through its retained initial extension.
Morgan--Tian Section 17.2, pp. 409-411. -/
noncomputable def inputExtension : SurgeryFlowExtension F0 :=
  ComposedExtension.append Q.initial Q.initial_eq (Q.globalExtension m13 0)

/-- The input extension reaches the very same constructed global flow.
Morgan--Tian Section 17.2, pp. 409-411. -/
theorem inputExtension_extended : (Q.inputExtension m13).extended = Q.globalFlow m13 :=
  ComposedExtension.append_extended Q.initial Q.initial_eq (Q.globalExtension m13 0)

end PoincareMT.M51.CompletedStageChain
