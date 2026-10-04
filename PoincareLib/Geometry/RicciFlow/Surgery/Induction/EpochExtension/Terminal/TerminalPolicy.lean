import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.OldEventPolicy

/-!
# Terminal policy on a returned observation

MT Definition 15.8 and Section 17.2, pp. 362 and 409-410. Old events keep
their geometric data, the constructed frontier has its own policy, and
the ordinary segment before the next observation has no further events.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Preserve policy through one observed surgery step. No policy is claimed
for times beyond the returned observation of a longer extension. -/
theorem M33OldEventDataPreservation.observedTerminalPolicy
    {F : SurgeryFlowData.{u}} {E : SurgeryFlowExtension F} {H : Real}
    (preserved : M33OldEventDataPreservation E)
    (O : SurgeryObservation E.extended)
    (hdomain : F.time_domain = Set.Ico 0 H)
    (policy : SurgeryFlowTerminalPolicyOn F F.time_domain)
    (frontier : SurgeryFlowTerminalPolicyOn E.extended ({H} : Set Real))
    (hfree : Disjoint E.extended.surgery_times (Set.Ioo H O.H)) :
    SurgeryFlowTerminalPolicyOn E.extended (surgeryObservationInterval O) := by
  have old := preserved.transportPolicy (Set.Subset.refl _) policy
  have event_location : ∀ t ∈ surgeryObservationInterval O,
      t ∈ E.extended.surgery_times → t ∈ F.time_domain ∨ t = H := by
    intro t ht hs
    rcases lt_trichotomy t H with hlt | heq | hgt
    · exact Or.inl (hdomain ▸ ⟨ht.1, hlt⟩)
    · exact Or.inr heq
    · exact (Set.disjoint_left.mp hfree hs ⟨hgt, ht.2⟩).elim
  constructor
  · intro t ht hs hpost
    rcases event_location t ht hs with hold | heq
    · exact old.nonempty t hold hs
    · exact frontier.nonempty t (Set.mem_singleton_iff.mpr heq) hs
  · intro t ht hs hempty
    rcases event_location t ht hs with hold | heq
    · exact old.vanishing t hold hs
    · exact frontier.vanishing t (Set.mem_singleton_iff.mpr heq) hs

end PoincareMT
