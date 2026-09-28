import PoincareConjecture.Proofs.M38.PartialCutLabels
import PoincareConjecture.Proofs.M38.EventForest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {P : ∀ i, EventCapCoordinates F T hT i}

namespace EventSpanningForest

variable (H : EventSpanningForest F T hT P) (e : H.graph.edgeSet)

def CutComponent : Type u := (H.graph.deleteEdges {e.val}).ConnectedComponent

instance : TopologicalSpace (H.CutComponent e) := ⊥

instance : DiscreteTopology (H.CutComponent e) := ⟨rfl⟩

noncomputable def cutVertexLabel (v : EventCutVertex F T hT) : H.CutComponent e :=
  (H.graph.deleteEdges {e.val}).connectedComponentMk v

theorem cutVertexLabel_other (f : H.graph.edgeSet) (hfe : f ≠ e) :
    H.cutVertexLabel e (cutSideVertex F T hT P (H.capEdge f) false) =
      H.cutVertexLabel e (cutSideVertex F T hT P (H.capEdge f) true) := by
  have hm : eventCapEnds F T hT P (H.capEdge f) ∈ (H.graph.deleteEdges {e.val}).edgeSet := by
    rw [H.capEdge_ends f, SimpleGraph.edgeSet_deleteEdges]
    exact ⟨f.property, fun h => hfe (Subtype.ext h)⟩
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    ((H.graph.deleteEdges {e.val}).mem_edgeSet.mp hm)

theorem cutVertexLabel_edge_ne :
    H.cutVertexLabel e (cutSideVertex F T hT P (H.capEdge e) false) ≠
      H.cutVertexLabel e (cutSideVertex F T hT P (H.capEdge e) true) := by
  have hb := SimpleGraph.isAcyclic_iff_forall_isBridge.mp H.acyclic e.property
  rw [← H.capEdge_ends e] at hb
  have hnr := SimpleGraph.isBridge_iff.mp hb
  change ¬ (H.graph.deleteEdges {eventCapEnds F T hT P (H.capEdge e)}).Reachable
    (cutSideVertex F T hT P (H.capEdge e) false)
    (cutSideVertex F T hT P (H.capEdge e) true) at hnr
  rw [H.capEdge_ends e] at hnr
  intro heq
  exact hnr (SimpleGraph.ConnectedComponent.exact heq)

theorem cutVertexLabel_uncut (S : Set (Fin (F.event T hT).cap_count))
    (he : H.capEdge e ∈ S) (hS : Sᶜ ⊆ H.selectedCaps)
    (i : Fin (F.event T hT).cap_count) (hi : i ∉ S) :
    H.cutVertexLabel e (.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
      H.cutVertexLabel e (.inr (ConnectedComponents.mk (P i).attachmentPoint)) := by
  obtain ⟨f, hfi⟩ := hS hi
  have hfe : f ≠ e := by
    intro h
    subst f
    exact hi (hfi ▸ he)
  rw [← hfi]
  exact H.cutVertexLabel_other e f hfe

theorem cut_centers_separated (S : Set (Fin (F.event T hT).cap_count))
    (he : H.capEdge e ∈ S) (hS : Sᶜ ⊆ H.selectedCaps) :
    ConnectedComponents.mk
        ((partialCapBall F T hT P S (⟨H.capEdge e, he⟩, false)).map 0) ≠
      ConnectedComponents.mk
        ((partialCapBall F T hT P S (⟨H.capEdge e, he⟩, true)).map 0) :=
  partialCut_centers_separated F T hT P S (H.cutVertexLabel e)
    (H.cutVertexLabel_uncut e S he hS) _ _ (H.cutVertexLabel_edge_ne e)

end EventSpanningForest

end PoincareConjecture.M38
