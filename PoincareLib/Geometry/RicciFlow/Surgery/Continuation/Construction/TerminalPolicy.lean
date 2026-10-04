import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.TerminalPolicy

/-!
# Terminal policy of the newly attached event

The continuation certificate stores the policy of its literal frontier event.
These projections expose that policy on the singleton frontier interval, which
is the input needed by the event-ledger transport below.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem RepairedNonemptyTerminalOperationCertificate.singletonTerminalPolicy
    {F : SurgeryFlowData.{u}} {T : ℝ}
    {I : RepairedContinuationInput F T}
    {E : SurgeryFlowExtension F}
    {hT : T ∈ E.extended.surgery_times}
    {hpost : Nonempty (E.extended.slice T).carrier}
    (operation : RepairedNonemptyTerminalOperationCertificate I E hT hpost) :
    SurgeryFlowTerminalPolicyOn E.extended ({T} : Set ℝ) := by
  constructor
  · intro t ht hT' hpost'
    have ht_eq : t = T := Set.mem_singleton_iff.mp ht
    subst t
    have hproof : hT' = hT := Subsingleton.elim _ _
    subst hT'
    exact ⟨by simpa only [operation.event_eq] using operation.terminal_policy⟩
  · intro t ht hT' hempty'
    have ht_eq : t = T := Set.mem_singleton_iff.mp ht
    subst t
    exact False.elim ((not_nonempty_iff.mpr hempty') hpost)

theorem RepairedVanishingTerminalOperationCertificate.singletonTerminalPolicy
    {F : SurgeryFlowData.{u}} {T : ℝ}
    {I : RepairedContinuationInput F T}
    {E : SurgeryFlowExtension F}
    {hT : T ∈ E.extended.surgery_times}
    {hempty : IsEmpty (E.extended.slice T).carrier}
    (operation : RepairedVanishingTerminalOperationCertificate I E hT hempty) :
    SurgeryFlowTerminalPolicyOn E.extended ({T} : Set ℝ) := by
  constructor
  · intro t ht hT' hpost'
    have ht_eq : t = T := Set.mem_singleton_iff.mp ht
    subst t
    exact False.elim ((not_nonempty_iff.mpr hempty) hpost')
  · intro t ht hT' hempty'
    have ht_eq : t = T := Set.mem_singleton_iff.mp ht
    subst t
    have hproof : hT' = hT := Subsingleton.elim _ _
    subst hT'
    simpa only [operation.event_eq] using operation.terminal_policy

theorem RepairedTerminalOperation.singletonTerminalPolicy
    {F : SurgeryFlowData.{u}} {T : ℝ}
    {I : RepairedContinuationInput F T}
    {E : SurgeryFlowExtension F}
    {hT : T ∈ E.extended.surgery_times}
    (operation : RepairedTerminalOperation I E hT) :
    SurgeryFlowTerminalPolicyOn E.extended ({T} : Set ℝ) := by
  cases operation with
  | nonempty hpost operation =>
      exact operation.singletonTerminalPolicy
  | vanishing hempty operation =>
      exact operation.singletonTerminalPolicy

end PoincareMT
