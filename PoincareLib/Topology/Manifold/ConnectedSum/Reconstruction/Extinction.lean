import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-! Adapted from Mapher `PoincareMT/Definitions/Ch18/FiniteExtinction.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology
universe u
namespace PoincareMT

structure FiniteExtinctionConclusion (F : SurgeryFlowData.{u}) where
  extinction_time : ℝ
  extinction_mem : extinction_time ∈ F.time_domain
  extinct : IsEmpty (F.slice extinction_time).carrier
  /-- The selected extinction time is an actual singular event, so
  reconstruction can consume that event rather than an arbitrary empty time. -/
  extinction_surgery_mem : extinction_time ∈ F.surgery_times
  permanent_empty : ∀ t : ℝ, ∀ _ht : t ∈ F.time_domain,
    extinction_time ≤ t → IsEmpty (F.slice t).carrier

/-- The terminal event is the flow's actual event at the selected extinction time. -/
def FiniteExtinctionConclusion.terminal_vanishing_event
    {F : SurgeryFlowData.{u}} (E : FiniteExtinctionConclusion F) :
    SurgeryVanishingEventData F.parameters F.slice F.metric E.extinction_time := by
  letI := E.extinct
  exact F.vanishing_event E.extinction_time E.extinction_surgery_mem

end PoincareMT
