import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.OldEventPolicy
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.TerminalPolicy

/-!
# Terminal policy throughout the M33 continuation

Definition 15.8 attaches one surgery and its maximal ordinary continuation.
Old-event policy follows from literal geometric preservation, frontier policy
from the constructed terminal operation, and there are no later events.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Source-faithful old events and the constructed frontier give the terminal
policy on the entire returned domain, without a policy-preservation premise. -/
theorem RepairedContinuationConclusion.terminalPolicy
    {F : SurgeryFlowData.{u}} {T : Real}
    {I : RepairedContinuationInput F T}
    (D : RepairedContinuationConclusion I)
    (policy : SurgeryFlowTerminalPolicyOn F F.time_domain) :
    SurgeryFlowTerminalPolicyOn D.extension.extended D.extension.extended.time_domain := by
  have old := D.old_event_data.transportPolicy (Set.Subset.refl _) policy
  have frontier := D.terminal_operation.singletonTerminalPolicy
  have event_location : ∀ t ∈ D.extension.extended.time_domain,
      t ∈ D.extension.extended.surgery_times → t ∈ F.time_domain ∨ t = T := by
    intro t ht hs
    have hle : t ≤ T := le_of_not_gt (fun hgt => D.no_later_surgery t ht hgt hs)
    rcases lt_or_eq_of_le hle with hlt | heq
    · left
      rw [I.time_domain_eq]
      exact ⟨D.extension.extended.time_domain_nonnegative ht, hlt⟩
    · exact Or.inr heq
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
