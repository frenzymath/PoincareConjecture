import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventIncidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Component labels of the actual incidence graph

The simple adjacency view is used only for the existing walk and quotient
API. Every cap edge remains in eventIncidenceGraph. The original pre-slice
component label descends because it agrees at the ends of every edge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- The simple adjacency view, transported from the full vertex-set subtype
back to the exact tagged component type. Indexed edges are not replaced. -/
noncomputable def eventIncidenceAdjacency : SimpleGraph (EventCutVertex F T hT) :=
  (eventIncidenceGraph F T hT P).toSimpleGraph.comap (fun v => ⟨v, Set.mem_univ _⟩)

/-- Adjacency means that one of the original cap edges has these two ends. -/
theorem eventIncidenceAdjacency_iff (x y : EventCutVertex F T hT) :
    (eventIncidenceAdjacency F T hT P).Adj x y ↔
      ∃ i, (eventIncidenceGraph F T hT P).IsLink i x y := by
  let : (eventIncidenceGraph F T hT P).Loopless := eventIncidenceGraph_loopless F T hT P
  exact Graph.toSimpleGraph_adj_iff _ _

/-- The connected-component quotient of the actual event incidence graph. -/
def EventGraphComponent : Type u := (eventIncidenceAdjacency F T hT P).ConnectedComponent

instance : TopologicalSpace (EventGraphComponent F T hT P) := ⊥

instance : DiscreteTopology (EventGraphComponent F T hT P) := ⟨rfl⟩

/-- The graph class of a literal retained or discarded component vertex. -/
noncomputable def eventGraphVertexClass (v : EventCutVertex F T hT) :
    EventGraphComponent F T hT P :=
  (eventIncidenceAdjacency F T hT P).connectedComponentMk v

/-- The negative and positive vertices of the same actual cap have one class. -/
theorem eventGraphVertexClass_edge (i : Fin (F.event T hT).cap_count) :
    eventGraphVertexClass F T hT P
        (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
      eventGraphVertexClass F T hT P
        (Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)) :=
  SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    ((eventIncidenceAdjacency_iff F T hT P _ _).mpr
      ⟨i, eventIncidenceGraph_link F T hT P i⟩)

/-- A walk in the actual adjacency graph stays within one original pre-component. -/
theorem eventGraph_walk_pre_component {x y : EventCutVertex F T hT}
    (p : (eventIncidenceAdjacency F T hT P).Walk x y) :
    eventVertexPreComponent F T hT x = eventVertexPreComponent F T hT y := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      obtain ⟨i, hi⟩ := (eventIncidenceAdjacency_iff F T hT P a b).mp hab
      exact (eventIncidenceGraph_pre_component F T hT P hi).trans ih

/-- The actual inclusion label descends to the graph's connected components. -/
noncomputable def eventGraphPreComponent :
    EventGraphComponent F T hT P → ConnectedComponents (F.slice (F.event T hT).tMinus).carrier :=
  SimpleGraph.ConnectedComponent.lift (eventVertexPreComponent F T hT)
    (fun _ _ p _ => eventGraph_walk_pre_component F T hT P p)

/-- On vertex representatives the descended map is the original inclusion. -/
theorem eventGraphPreComponent_vertex (v : EventCutVertex F T hT) :
    eventGraphPreComponent F T hT P (eventGraphVertexClass F T hT P v) =
      eventVertexPreComponent F T hT v := rfl

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count} (Q : EventCapCoordinates F T hT i)

/-- Every point of the literal negative half has its fixed attaching label. -/
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

/-- Every point of the literal positive half has its fixed attaching label. -/
theorem positive_discarded_component_eq (x : eventDiscardedOpen F T hT)
    (hx : x.val ∈ Q.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) :
    ConnectedComponents.mk x = ConnectedComponents.mk Q.attachmentPoint := by
  apply Q.attachment_component_eq
  rwa [Q.attachmentChart_target]

/-- Every point in one full actual collar lies in the pre-component of
its negative attaching point, including the central sphere. -/
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

end PoincareMT.M38
