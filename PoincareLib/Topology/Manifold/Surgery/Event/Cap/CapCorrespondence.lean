import PoincareLib.Topology.Manifold.Surgery.Event.Riemannian.RiemannianBalls
import PoincareLib.Topology.Manifold.Surgery.Event.Survivors.Survivors
import Mathlib.Tactic.Linarith

/-!
# Actual cap correspondence

The cap at a raw event is the image under the supplied local embedding of the
closure of the actual standard cap chart. Connectedness is enough to place it
in one survivor component. No selected metric-surgery theorem is applied.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

/-- Each actual inserted cap is connected. This uses the event's own local
result and embedding, and the standard open ball before taking its closure. -/
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

/-- The auxiliary cap correspondence follows from any actual reconstruction
and the raw event geometry. The reconstruction remains the substantive input
to this helper, not an additional hypothesis of the M38 theorem. -/
theorem capCorrespondence
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)) :
    RawNonemptyCapCorrespondence F T hT C where
  cap_piece i := exists_survivor_containing C (isConnected_cap F T hT i)

/-- Package an actual nonempty-event conclusion with its derived cap field. -/
def nonemptyWitness
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)) :
    RawNonemptyTopologyWitness F T hT where
  conclusion := C
  cap_correspondence := capCorrespondence F T hT C

end PoincareMT.M38
