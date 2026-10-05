import PoincareLib.Topology.Manifold.Surgery.Event.Assembly.AssemblyTransport
import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapCorrespondence

/-!
# Transport from the actual late slice

The target-transport constructions depend only on Chapter 15's geometric
records. They preserve the summands and survivor maps, and
transport the final operation or the initial union. Here they are applied
to the actual event's pre_identify inverse. No later theorem is imported.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

/-- A conclusion on an event's actual late slice gives the nonempty
witness on its stored pre-slice, with cap correspondence derived from
the actual caps. Source: Proposition 15.3, pp. 357-358. -/
noncomputable def nonemptyWitnessAtLateTime
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (t : Set.Ico (F.event T hT).tMinus T)
    (C : SurgeryTopologyConclusion (F.slice t.val) (F.slice T)) :
    RawNonemptyTopologyWitness F T hT :=
  nonemptyWitness F T hT (transportConclusion C ((F.event T hT).pre_identify t).symm)

/-- The vanishing branch uses its own actual late-slice map. The empty
post-slice excludes every survivor in the transported conclusion.
Source: Proposition 15.3, pp. 357-358, wholly disappearing slice. -/
noncomputable def vanishingWitnessAtLateTime
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier]
    (t : Set.Ico (F.vanishing_event T hT).tMinus T)
    (C : SurgeryTopologyConclusion (F.slice t.val) (F.slice T)) :
    RawVanishingTopologyWitness F T hT :=
  vanishingWitness (transportConclusion C ((F.vanishing_event T hT).pre_identify t).symm)

end PoincareMT.M38
