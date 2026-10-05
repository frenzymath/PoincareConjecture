import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventGraphCover
import PoincareLib.Topology.Manifold.Surgery.Event.Partial.PartialCutDomains

/-!
# Continuous vertex labels on the actual partially cut old domain

The two interiors and the full uncut collars cover this domain. Any
discrete vertex label that agrees across the uncut edges extends over
that cover, retaining the literal component labels on both interiors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  {D : Type v} [TopologicalSpace D] (label : EventCutVertex F T hT → D)

local instance : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
  ChartedSpace.locallyConnectedSpace StandardCapSpace _

local instance : LocallyConnectedSpace (eventRetainedInteriorOpen F T hT) :=
  (eventRetainedInteriorOpen F T hT).isOpen.locallyConnectedSpace

local instance : LocallyConnectedSpace (eventDiscardedOpen F T hT) :=
  (eventDiscardedOpen F T hT).isOpen.locallyConnectedSpace

/-- The prescribed label of the actual retained component. -/
noncomputable def retainedVertexLabel : C(eventRetainedInteriorOpen F T hT, D) :=
  ⟨fun x => label (Sum.inl (ConnectedComponents.mk x)),
    (continuous_of_discreteTopology : Continuous
      (fun c : ConnectedComponents (eventRetainedInteriorOpen F T hT) => label (Sum.inl c))).comp
        ConnectedComponents.continuous_coe⟩

/-- The prescribed label of the actual discarded component. -/
noncomputable def discardedVertexLabel : C(eventDiscardedOpen F T hT, D) :=
  ⟨fun x => label (Sum.inr (ConnectedComponents.mk x)),
    (continuous_of_discreteTopology : Continuous
      (fun c : ConnectedComponents (eventDiscardedOpen F T hT) => label (Sum.inr c))).comp
        ConnectedComponents.continuous_coe⟩

/-- The two actual interiors and precisely the uncut full collars in the old domain. -/
noncomputable def cutOldPatch (j : Bool ⊕ {i // i ∉ S}) :
    TopologicalSpace.Opens (eventCutOpen F T hT P S) :=
  let k : Bool ⊕ Fin (F.event T hT).cap_count := j.map id Subtype.val
  ⟨Subtype.val ⁻¹' (eventPrePatch F T hT P k : Set _),
    (eventPrePatch F T hT P k).isOpen.preimage continuous_subtype_val⟩

/-- Each interior uses its component label; an uncut collar uses its negative endpoint. -/
noncomputable def cutOldPatchLabel (j : Bool ⊕ {i // i ∉ S}) :
    C(cutOldPatch F T hT P S j, D) :=
  match j with
  | .inl false => (retainedVertexLabel F T hT label).comp
      ⟨fun x => ⟨x.val.val, x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  | .inl true => (discardedVertexLabel F T hT label).comp
      ⟨fun x => ⟨x.val.val, x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  | .inr i => ContinuousMap.const _
      (label (.inl (ConnectedComponents.mk (P i.val).retainedAttachmentPoint)))

/-- On a retained overlap the patch has the actual retained point's label. -/
theorem cutOldPatchLabel_on_retained (j : Bool ⊕ {i // i ∉ S})
    (x : eventCutOpen F T hT P S) (hxj : x ∈ cutOldPatch F T hT P S j)
    (hx : x.val ∈ eventRetainedInteriorOpen F T hT) :
    cutOldPatchLabel F T hT P S label j ⟨x, hxj⟩ =
      label (.inl (ConnectedComponents.mk (⟨x.val, hx⟩ : eventRetainedInteriorOpen F T hT))) := by
  cases j with
  | inl b =>
      cases b with
      | false => rfl
      | true => exact (hxj (interior_subset hx)).elim
  | inr i =>
      have hneg : x.val ∈ (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) := by
        rw [← (P i.val).collar_retained_inter]
        exact ⟨hxj, hx⟩
      exact congrArg (fun c => label (.inl c))
        ((P i.val).negative_retained_component_eq ⟨x.val, hx⟩ hneg).symm

variable (hagrees : ∀ i, i ∉ S →
  label (.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
    label (.inr (ConnectedComponents.mk (P i).attachmentPoint)))

include hagrees in
/-- The uncut-edge assumption identifies labels on discarded overlaps. -/
theorem cutOldPatchLabel_on_discarded (j : Bool ⊕ {i // i ∉ S})
    (x : eventCutOpen F T hT P S) (hxj : x ∈ cutOldPatch F T hT P S j)
    (hx : x.val ∈ eventDiscardedOpen F T hT) :
    cutOldPatchLabel F T hT P S label j ⟨x, hxj⟩ =
      label (.inr (ConnectedComponents.mk (⟨x.val, hx⟩ : eventDiscardedOpen F T hT))) := by
  cases j with
  | inl b =>
      cases b with
      | false => exact (hx (interior_subset hxj)).elim
      | true => rfl
  | inr i =>
      have hpos : x.val ∈ (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
        rw [← (P i.val).collar_discarded_inter]
        exact ⟨hxj, hx⟩
      exact (hagrees i.val i.property).trans (congrArg (fun c => label (.inr c))
        ((P i.val).positive_discarded_component_eq ⟨x.val, hx⟩ hpos).symm)

include hagrees in
/-- All labels agree on full patch intersections, including uncut central spheres. -/
theorem cutOldPatchLabel_agree (j k : Bool ⊕ {i // i ∉ S})
    (x : eventCutOpen F T hT P S)
    (hxj : x ∈ cutOldPatch F T hT P S j) (hxk : x ∈ cutOldPatch F T hT P S k) :
    cutOldPatchLabel F T hT P S label j ⟨x, hxj⟩ =
      cutOldPatchLabel F T hT P S label k ⟨x, hxk⟩ := by
  by_cases hr : x.val ∈ eventRetainedInteriorOpen F T hT
  · rw [cutOldPatchLabel_on_retained F T hT P S label j x hxj hr,
      cutOldPatchLabel_on_retained F T hT P S label k x hxk hr]
  by_cases hd : x.val ∈ eventDiscardedOpen F T hT
  · rw [cutOldPatchLabel_on_discarded F T hT P S label hagrees j x hxj hd,
      cutOldPatchLabel_on_discarded F T hT P S label hagrees k x hxk hd]
  cases j with
  | inl b => cases b <;> first | exact (hr hxj).elim | exact (hd hxj).elim
  | inr i =>
      cases k with
      | inl b => cases b <;> first | exact (hr hxk).elim | exact (hd hxk).elim
      | inr j =>
          by_cases hij : i.val = j.val
          · have heq : i = j := Subtype.ext hij
            subst j
            rfl
          · exact (Set.disjoint_left.mp
              ((P i.val).collars_disjoint (P j.val) hij) hxj hxk).elim

/-- The frontier equation and the selected-sphere exclusion give the full old cover. -/
theorem cutOldPatch_cover (x : eventCutOpen F T hT P S) :
    ∃ j, (cutOldPatch F T hT P S j : Set (eventCutOpen F T hT P S)) ∈ 𝓝 x := by
  by_cases hr : x.val ∈ eventRetainedInteriorOpen F T hT
  · exact ⟨.inl false, (cutOldPatch F T hT P S (.inl false)).isOpen.mem_nhds hr⟩
  by_cases hd : x.val ∈ eventDiscardedOpen F T hT
  · exact ⟨.inl true, (cutOldPatch F T hT P S (.inl true)).isOpen.mem_nhds hd⟩
  have hret : x.val ∈ (F.event T hT).retained_pre := by
    by_contra h
    exact hd h
  have hf : x.val ∈ frontier (F.event T hT).retained_pre := by
    rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    exact ⟨hret, hr⟩
  rw [(F.event T hT).pre_boundary] at hf
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
  rw [← (P i).collar_central] at hi
  have hiS : i ∉ S := by
    intro h
    exact x.property (Set.mem_iUnion.mpr ⟨⟨i, h⟩, hi⟩)
  refine ⟨.inr ⟨i, hiS⟩, (cutOldPatch F T hT P S (.inr ⟨i, hiS⟩)).isOpen.mem_nhds ?_⟩
  apply Set.image_mono _ hi
  intro z hz
  have hz0 : z.2 = 0 := hz.2
  exact ⟨hz.1, by simpa only [hz0] using (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)⟩

/-- The continuous vertex label on the literal old domain for the selected cuts. -/
noncomputable def cutOldLabel : C(eventCutOpen F T hT P S, D) :=
  ContinuousMap.liftCover (fun j => cutOldPatch F T hT P S j)
    (cutOldPatchLabel F T hT P S label) (cutOldPatchLabel_agree F T hT P S label hagrees)
    (cutOldPatch_cover F T hT P S)

/-- Cover gluing keeps the exact label on every patch. -/
theorem cutOldLabel_patch (j : Bool ⊕ {i // i ∉ S})
    (x : cutOldPatch F T hT P S j) :
    cutOldLabel F T hT P S label hagrees x.val = cutOldPatchLabel F T hT P S label j x :=
  ContinuousMap.liftCover_coe
    (S := fun j : Bool ⊕ {i // i ∉ S} =>
      (cutOldPatch F T hT P S j : Set (eventCutOpen F T hT P S)))
    (φ := cutOldPatchLabel F T hT P S label)
    (hφ := cutOldPatchLabel_agree F T hT P S label hagrees)
    (hS := cutOldPatch_cover F T hT P S) (i := j) x

/-- On every retained old point, the actual retained component label is unchanged. -/
theorem cutOldLabel_retained (x : eventCutOpen F T hT P S)
    (hx : x.val ∈ eventRetainedInteriorOpen F T hT) :
    cutOldLabel F T hT P S label hagrees x =
      label (.inl (ConnectedComponents.mk (⟨x.val, hx⟩ : eventRetainedInteriorOpen F T hT))) :=
  cutOldLabel_patch F T hT P S label hagrees (.inl false) ⟨x, hx⟩

/-- On every discarded old point, the actual discarded component label is unchanged. -/
theorem cutOldLabel_discarded (x : eventCutOpen F T hT P S)
    (hx : x.val ∈ eventDiscardedOpen F T hT) :
    cutOldLabel F T hT P S label hagrees x =
      label (.inr (ConnectedComponents.mk (⟨x.val, hx⟩ : eventDiscardedOpen F T hT))) :=
  cutOldLabel_patch F T hT P S label hagrees (.inl true) ⟨x, hx⟩

/-- The whole uncut collar keeps its endpoint label, including the central sphere. -/
theorem cutOldLabel_collar (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)
    (x : eventCutOpen F T hT P S)
    (hx : x.val ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
    cutOldLabel F T hT P S label hagrees x =
      label (.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) :=
  cutOldLabel_patch F T hT P S label hagrees (.inr ⟨i, hi⟩) ⟨x, hx⟩

end PoincareMT.M38
