import PoincareConjecture.Proofs.M38.AssemblyTransport
import PoincareConjecture.Proofs.M38.CapCorrespondence

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

noncomputable def nonemptyWitnessAtLateTime
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (t : Set.Ico (F.event T hT).tMinus T)
    (C : SurgeryTopologyConclusion (F.slice t.val) (F.slice T)) :
    RawNonemptyTopologyWitness F T hT :=
  nonemptyWitness F T hT (transportConclusion C ((F.event T hT).pre_identify t).symm)

noncomputable def vanishingWitnessAtLateTime
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier]
    (t : Set.Ico (F.vanishing_event T hT).tMinus T)
    (C : SurgeryTopologyConclusion (F.slice t.val) (F.slice T)) :
    RawVanishingTopologyWitness F T hT :=
  vanishingWitness (transportConclusion C ((F.vanishing_event T hT).pre_identify t).symm)

end PoincareConjecture.M38
