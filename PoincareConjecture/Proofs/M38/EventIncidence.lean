import PoincareConjecture.Proofs.M38.RetainedBoundary
import PoincareConjecture.Proofs.M38.CappingComponents
import Mathlib.Combinatorics.Graph.Simple









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)


def EventCutVertex : Type u :=
  ConnectedComponents (eventRetainedInteriorOpen F T hT) ⊕
    ConnectedComponents (eventDiscardedOpen F T hT)

include P in

theorem eventCutVertex_finite : Finite (EventCutVertex F T hT) := by
  let : Finite (ConnectedComponents (eventRetainedInteriorOpen F T hT)) :=
    eventRetainedInterior_finite_components F T hT P
  let : Finite (ConnectedComponents (eventDiscardedOpen F T hT)) :=
    eventDiscardedOpen_finite_components F T hT P
  exact inferInstanceAs (Finite
    (ConnectedComponents (eventRetainedInteriorOpen F T hT) ⊕
      ConnectedComponents (eventDiscardedOpen F T hT)))


noncomputable def eventIncidenceGraph :
    Graph (EventCutVertex F T hT) (Fin (F.event T hT).cap_count) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink i x y :=
    (x = Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint) ∧
      y = Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)) ∨
    (x = Sum.inr (ConnectedComponents.mk (P i).attachmentPoint) ∧
      y = Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint))
  isLink_symm := by
    intro i _
    refine ⟨fun x y h => ?_⟩
    exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)
  eq_or_eq_of_isLink_of_isLink := by
    intro i x y v w h h'
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      rcases h' with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · exact Or.inl (hx.trans hv.symm)
    · exact Or.inr (hx.trans hw.symm)
    · exact Or.inr (hx.trans hw.symm)
    · exact Or.inl (hx.trans hv.symm)
  edge_mem_iff_exists_isLink := fun i =>
    ⟨fun _ => ⟨Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint),
      Sum.inr (ConnectedComponents.mk (P i).attachmentPoint), Or.inl ⟨rfl, rfl⟩⟩,
      fun _ => Set.mem_univ _⟩
  left_mem_of_isLink := by
    intro i x y h
    exact Set.mem_univ _


theorem eventIncidenceGraph_edges : (eventIncidenceGraph F T hT P).edgeSet = Set.univ := rfl



theorem eventIncidenceGraph_vertices : (eventIncidenceGraph F T hT P).vertexSet = Set.univ := rfl


theorem eventIncidenceGraph_link (i : Fin (F.event T hT).cap_count) :
    (eventIncidenceGraph F T hT P).IsLink i
      (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint))
      (Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)) := Or.inl ⟨rfl, rfl⟩



theorem eventIncidenceGraph_loopless : (eventIncidenceGraph F T hT P).Loopless := by
  refine ⟨?_⟩
  intro e x h
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Sum.inl_ne_inr (hx.symm.trans hy)
  · exact Sum.inr_ne_inl (hx.symm.trans hy)



noncomputable def eventCappedVertexEquiv :
    EventCutVertex F T hT ≃
      (ConnectedComponents (F.slice T).carrier ⊕
        ConnectedComponents (CappedDiscardedSpace F T hT P)) :=
  Equiv.sumCongr (retainedComponentsHomeomorph F T hT P).toEquiv
    (cappedComponentsHomeomorph F T hT P).toEquiv



theorem eventCappedVertexEquiv_retained (i : Fin (F.event T hT).cap_count) :
    eventCappedVertexEquiv F T hT P
        (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
      Sum.inl (ConnectedComponents.mk (P i).retainedAnnularPoint.val) := by
  change Sum.inl (ConnectedComponents.mk
    ((F.event T hT).retention.map (P i).retainedAttachmentPoint.val)) = _
  rw [(P i).retainedAttachmentPoint_image]



theorem eventCappedVertexEquiv_discarded (i : Fin (F.event T hT).cap_count) :
    eventCappedVertexEquiv F T hT P
        (Sum.inr (ConnectedComponents.mk (P i).attachmentPoint)) =
      Sum.inr (ConnectedComponents.mk (cappedOldInclusion F T hT P (P i).attachmentPoint)) := rfl



noncomputable def eventVertexPreComponent :
    EventCutVertex F T hT → ConnectedComponents (F.slice (F.event T hT).tMinus).carrier :=
  Sum.elim
    (continuous_subtype_val : Continuous (Subtype.val :
      eventRetainedInteriorOpen F T hT →
        (F.slice (F.event T hT).tMinus).carrier)).connectedComponentsMap
    (continuous_subtype_val : Continuous (Subtype.val :
      eventDiscardedOpen F T hT → (F.slice (F.event T hT).tMinus).carrier)).connectedComponentsMap

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count} (Q : EventCapCoordinates F T hT i)



theorem attaching_points_pre_component_eq :
    ConnectedComponents.mk Q.retainedAttachmentPoint.val =
      ConnectedComponents.mk Q.attachmentPoint.val := by
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
  have hpos : Q.attachmentPoint.val ∈ Q.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    Set.image_mono positive_collar_subset Q.attachmentPoint_positive
  exact ConnectedComponents.coe_eq_coe'.mpr (hc.subset_connectedComponent hpos hneg)

end EventCapCoordinates



theorem eventIncidenceGraph_pre_component {i : Fin (F.event T hT).cap_count}
    {x y : EventCutVertex F T hT} (h : (eventIncidenceGraph F T hT P).IsLink i x y) :
    eventVertexPreComponent F T hT x = eventVertexPreComponent F T hT y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (P i).attaching_points_pre_component_eq
  · exact (P i).attaching_points_pre_component_eq.symm

end PoincareConjecture.M38
