import PoincareConjecture.Proofs.M38.EventIncidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)



noncomputable def eventIncidenceAdjacency : SimpleGraph (EventCutVertex F T hT) :=
  (eventIncidenceGraph F T hT P).toSimpleGraph.comap (fun v => ⟨v, Set.mem_univ _⟩)


theorem eventIncidenceAdjacency_iff (x y : EventCutVertex F T hT) :
    (eventIncidenceAdjacency F T hT P).Adj x y ↔
      ∃ i, (eventIncidenceGraph F T hT P).IsLink i x y := by
  let : (eventIncidenceGraph F T hT P).Loopless := eventIncidenceGraph_loopless F T hT P
  exact Graph.toSimpleGraph_adj_iff _ _


def EventGraphComponent : Type u := (eventIncidenceAdjacency F T hT P).ConnectedComponent

instance : TopologicalSpace (EventGraphComponent F T hT P) := ⊥

instance : DiscreteTopology (EventGraphComponent F T hT P) := ⟨rfl⟩


noncomputable def eventGraphVertexClass (v : EventCutVertex F T hT) :
    EventGraphComponent F T hT P :=
  (eventIncidenceAdjacency F T hT P).connectedComponentMk v


theorem eventGraphVertexClass_edge (i : Fin (F.event T hT).cap_count) :
    eventGraphVertexClass F T hT P
        (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
      eventGraphVertexClass F T hT P
        (Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    ((eventIncidenceAdjacency_iff F T hT P _ _).mpr
      ⟨i, eventIncidenceGraph_link F T hT P i⟩)


theorem eventGraph_walk_pre_component {x y : EventCutVertex F T hT}
    (p : (eventIncidenceAdjacency F T hT P).Walk x y) :
    eventVertexPreComponent F T hT x = eventVertexPreComponent F T hT y := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      obtain ⟨i, hi⟩ := (eventIncidenceAdjacency_iff F T hT P a b).mp hab
      exact (eventIncidenceGraph_pre_component F T hT P hi).trans ih


noncomputable def eventGraphPreComponent :
    EventGraphComponent F T hT P → ConnectedComponents (F.slice (F.event T hT).tMinus).carrier :=
  SimpleGraph.ConnectedComponent.lift (eventVertexPreComponent F T hT)
    (fun _ _ p _ => eventGraph_walk_pre_component F T hT P p)


theorem eventGraphPreComponent_vertex (v : EventCutVertex F T hT) :
    eventGraphPreComponent F T hT P (eventGraphVertexClass F T hT P v) =
      eventVertexPreComponent F T hT v := rfl

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count} (Q : EventCapCoordinates F T hT i)


theorem negative_retained_component_eq (x : eventRetainedInteriorOpen F T hT)
    (hx : x.val ∈ Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0)) :
    ConnectedComponents.mk x = ConnectedComponents.mk Q.retainedAttachmentPoint := by
  have h := Q.negative_collar_subset_retained_component Q.retainedAttachmentPoint rfl hx
  rw [connectedComponentIn_eq_image
    (show Q.retainedAttachmentPoint.val ∈ interior (F.event T hT).retained_pre from
      Q.retainedAttachmentPoint.property)] at h
  obtain ⟨y, hy, heq⟩ := h
  have heq' : y = x := Subtype.ext heq
  rw [heq'] at hy
  exact ConnectedComponents.coe_eq_coe'.mpr hy


theorem positive_discarded_component_eq (x : eventDiscardedOpen F T hT)
    (hx : x.val ∈ Q.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ConnectedComponents.mk x = ConnectedComponents.mk Q.attachmentPoint := by
  apply Q.attachment_component_eq
  rwa [Q.attachmentChart_target]



theorem full_collar_pre_component (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
    ConnectedComponents.mk x = ConnectedComponents.mk Q.retainedAttachmentPoint.val := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  have hc : IsConnected (Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
    (isConnected_univ.prod (isConnected_Ioo (by norm_num))).image _
      Q.collarChart.continuousOn_toFun
  have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 0 ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
  have hneg : Q.retainedAttachmentPoint.val ∈
      Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    Set.image_mono hsub Q.retainedAttachmentPoint_negative
  exact ConnectedComponents.coe_eq_coe'.mpr (hc.subset_connectedComponent hneg hx)

end EventCapCoordinates

end PoincareConjecture.M38
