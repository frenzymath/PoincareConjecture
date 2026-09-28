import PoincareConjecture.Proofs.M38.PartialCutConnectivity
import PoincareConjecture.Proofs.M38.EventForest
import PoincareConjecture.Proofs.M38.SingleCutNeighborhood

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38.EventSpanningForest

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {P : ∀ i, EventCapCoordinates F T hT i}
  (H : EventSpanningForest F T hT P)
  (S : Set (Fin (F.event T hT).cap_count)) (hS : S ⊆ H.residualCaps)

include hS

theorem selected_not_mem_residual_selection (e : H.graph.edgeSet) : H.capEdge e ∉ S :=
  fun hi => hS hi (Set.mem_range_self e)

theorem residual_vertexComponent_adj {x y : EventCutVertex F T hT}
    (hxy : H.graph.Adj x y) :
    partialCutVertexComponent F T hT P S x = partialCutVertexComponent F T hT P S y := by
  let e : H.graph.edgeSet := ⟨s(x, y), hxy⟩
  have hi : H.capEdge e ∉ S := H.selected_not_mem_residual_selection S hS e
  have h := partialCutVertexComponent_uncut F T hT P S (H.capEdge e) hi
  have hlink := H.capEdge_link hxy
  rcases hlink with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact (congrArg (partialCutVertexComponent F T hT P S) hx).trans
      (h.trans (congrArg (partialCutVertexComponent F T hT P S) hy).symm)
  · exact (congrArg (partialCutVertexComponent F T hT P S) hx).trans
      (h.symm.trans (congrArg (partialCutVertexComponent F T hT P S) hy).symm)

theorem residual_vertexComponent_walk {x y : EventCutVertex F T hT}
    (p : H.graph.Walk x y) :
    partialCutVertexComponent F T hT P S x = partialCutVertexComponent F T hT P S y := by
  induction p with
  | nil => rfl
  | cons hxy p ih => exact (H.residual_vertexComponent_adj S hS hxy).trans ih

theorem residual_centers_connected (i : S) :
    ConnectedComponents.mk ((partialCapBall F T hT P S (i, false)).map 0) =
      ConnectedComponents.mk ((partialCapBall F T hT P S (i, true)).map 0) := by
  rw [partialCut_ball_center_component, partialCut_ball_center_component]
  obtain ⟨p, _⟩ := H.exists_capPath i.val
  exact H.residual_vertexComponent_walk S hS p

theorem residual_singleCut_centers (i : Fin (F.event T hT).cap_count)
    (hi : i ∈ H.residualCaps) :
    ConnectedComponents.mk ((singleCutBall F T hT P S i false).map 0) =
      ConnectedComponents.mk ((singleCutBall F T hT P S i true).map 0) := by
  have hsub : insert i S ⊆ H.residualCaps := Set.insert_subset hi hS
  exact H.residual_centers_connected (insert i S) hsub ⟨i, Set.mem_insert i S⟩

theorem residual_singleCut_enclosing_ball (i : Fin (F.event T hT).cap_count)
    (hi : i ∈ H.residualCaps) :
    ∃ C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)),
      (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ∪
        (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
          C.map '' Metric.ball 0 1 :=
  singleCut_exists_enclosing_ball F T hT P S i (H.residual_singleCut_centers S hS i hi)

end PoincareConjecture.M38.EventSpanningForest
