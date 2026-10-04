import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyExtension
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.OldEventPolicy

/-!
# Terminal policy in the permanent empty continuation

Morgan--Tian Definition 15.8 and Section 17.2, pp. 362 and 409.
The copied events retain their actual terminal geometry and pre-flow.
Every event of the extended flow belongs to the old event set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PoincareMT

namespace SurgeryEventData

/-- Relabeling the past preserves the primitive terminal-policy data. -/
theorem reindexPast_preservation
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : Real -> GeneralizedSliceCarrier.{u}}
    {metric : forall t, RiemannianMetric 3 (slice t).carrier} {T : Real}
    (E : SurgeryEventData g0 K P slice metric T)
    (tau : Real -> Real) (hTau : forall t, t <= T -> tau t = t) :
    M33NonemptyEventDataPreservation E (E.reindexPast tau hTau) := by
  refine {
    terminal_eq := rfl
    limit_metric_heq := HEq.rfl
    limit_connection_heq := HEq.rfl
    cap_count_eq := rfl
    necks_heq := HEq.rfl
    retained_image_heq := ?_ }
  apply heq_of_eq
  rw [<- E.reindexPast_retained_pre_image tau hTau, Set.image_image]
  apply Set.image_congr
  intro x _
  exact E.reindexPast_limit_identify_map tau hTau x

end SurgeryEventData

namespace SurgeryVanishingEventData

/-- The copied vanishing event has the same reference carrier and pre-flow. -/
theorem reindexPast_preservation
    {P : SurgeryParameters} {slice : Real -> GeneralizedSliceCarrier.{u}}
    {metric : forall t, RiemannianMetric 3 (slice t).carrier} {T : Real}
    (E : SurgeryVanishingEventData P slice metric T)
    (tau : Real -> Real) (hTau : forall t, t <= T -> tau t = t) :
    M33VanishingEventDataPreservation E (E.reindexPast tau hTau) where
  reference_eq := rfl
  pre_carrier_eq := congrArg slice (hTau E.tMinus E.tMinus_lt.le)
  pre_flow_heq := E.reindexPast_pre_flow_heq tau hTau

end SurgeryVanishingEventData

namespace M51Empty

variable (F : SurgeryFlowData.{u}) {a : Real} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

/-- The actual permanent-empty extension preserves both old event branches. -/
theorem oldEventDataPreservation :
    M33OldEventDataPreservation (extension F ha) := by
  constructor
  · intro T hT hOld hNew hT'
    let : Nonempty (slice F a T).carrier := hNew
    change M33NonemptyEventDataPreservation (F.event T hT) (event F ha T hT')
    cases Subsingleton.elim hT' hT
    exact (F.event T hT).reindexPast_preservation
      (fun t => min t a) (event_clock F ha T hT)
  · intro T hT hOld hNew hT'
    let : IsEmpty (slice F a T).carrier := hNew
    change M33VanishingEventDataPreservation
      (F.vanishing_event T hT) (vanishingEvent F ha T hT')
    cases Subsingleton.elim hT' hT
    exact (F.vanishing_event T hT).reindexPast_preservation
      (fun t => min t a) (event_clock F ha T hT)

/-- No new event appears after the included empty slice, so old policy
covers every event in the full extended domain, including the event at a. -/
theorem terminalPolicy
    (policy : SurgeryFlowTerminalPolicyOn F F.time_domain) :
    SurgeryFlowTerminalPolicyOn (flow F ha) (flow F ha).time_domain := by
  have old := (oldEventDataPreservation F ha).transportPolicy (Set.Subset.refl _) policy
  change SurgeryFlowTerminalPolicyOn (extension F ha).extended
    (extension F ha).extended.time_domain
  constructor
  · intro T _ hT hpost
    exact old.nonempty T (F.surgery_times_subset hT) hT
  · intro T _ hT hempty
    exact old.vanishing T (F.surgery_times_subset hT) hT

end M51Empty

end PoincareMT
