import PoincareConjecture.Proofs.M38.RiemannianBalls
import PoincareConjecture.Proofs.M38.Survivors
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38



theorem isConnected_cap
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count) :
    IsConnected ((F.event T hT).caps i).carrier := by
  have hr : 0 < F.standard_initial.cylindrical_end.radius + 4 := by
    linarith [F.standard_initial.cylindrical_end.radius_pos]
  have hball := (isPathConnected_ball F.standard_initial.metric 0 hr).isConnected
  have hsubset :
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 4) ⊆
      F.standard_initial.metric.ball 0 (F.standard_initial.cylindrical_end.radius + 5) := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have himage := hball.image ((F.event T hT).local_result i).cap_map
    (((F.event T hT).local_result i).cap_map_smooth.continuousOn.mono hsubset)
  rw [← (F.event T hT).local_cap_image i]
  exact himage.closure.image ((F.event T hT).local_embed i)
    ((F.event T hT).local_embed_smooth i).continuous.continuousOn




theorem capCorrespondence
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)) :
    RawNonemptyCapCorrespondence F T hT C where
  cap_piece i := exists_survivor_containing C (isConnected_cap F T hT i)


def nonemptyWitness
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)) :
    RawNonemptyTopologyWitness F T hT where
  conclusion := C
  cap_correspondence := capCorrespondence F T hT C

end PoincareConjecture.M38
