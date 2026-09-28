import PoincareConjecture.Proofs.M38.EventGraphLabels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

local instance : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
  ChartedSpace.locallyConnectedSpace StandardCapSpace _

local instance : LocallyConnectedSpace (eventRetainedInteriorOpen F T hT) :=
  (eventRetainedInteriorOpen F T hT).isOpen.locallyConnectedSpace

local instance : LocallyConnectedSpace (eventDiscardedOpen F T hT) :=
  (eventDiscardedOpen F T hT).isOpen.locallyConnectedSpace

noncomputable def retainedGraphLabel :
    C(eventRetainedInteriorOpen F T hT, EventGraphComponent F T hT P) :=
  ⟨fun x => eventGraphVertexClass F T hT P (Sum.inl (ConnectedComponents.mk x)),
    (continuous_of_discreteTopology : Continuous
      (fun c : ConnectedComponents (eventRetainedInteriorOpen F T hT) =>
        eventGraphVertexClass F T hT P (Sum.inl c))).comp ConnectedComponents.continuous_coe⟩

noncomputable def discardedGraphLabel :
    C(eventDiscardedOpen F T hT, EventGraphComponent F T hT P) :=
  ⟨fun x => eventGraphVertexClass F T hT P (Sum.inr (ConnectedComponents.mk x)),
    (continuous_of_discreteTopology : Continuous
      (fun c : ConnectedComponents (eventDiscardedOpen F T hT) =>
        eventGraphVertexClass F T hT P (Sum.inr c))).comp ConnectedComponents.continuous_coe⟩

def eventPrePatch : Bool ⊕ Fin (F.event T hT).cap_count →
    TopologicalSpace.Opens (F.slice (F.event T hT).tMinus).carrier
  | Sum.inl false => eventRetainedInteriorOpen F T hT
  | Sum.inl true => eventDiscardedOpen F T hT
  | Sum.inr i => ⟨(P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1),
      (P i).collarChart.open_target⟩

noncomputable def eventPrePatchLabel (j : Bool ⊕ Fin (F.event T hT).cap_count) :
    C(eventPrePatch F T hT P j, EventGraphComponent F T hT P) :=
  match j with
  | Sum.inl false => retainedGraphLabel F T hT P
  | Sum.inl true => discardedGraphLabel F T hT P
  | Sum.inr i => ContinuousMap.const _ (eventGraphVertexClass F T hT P
      (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)))

theorem eventPrePatchLabel_on_retained (j : Bool ⊕ Fin (F.event T hT).cap_count)
    (x : (F.slice (F.event T hT).tMinus).carrier) (hxj : x ∈ eventPrePatch F T hT P j)
    (hx : x ∈ eventRetainedInteriorOpen F T hT) :
    eventPrePatchLabel F T hT P j ⟨x, hxj⟩ = retainedGraphLabel F T hT P ⟨x, hx⟩ := by
  cases j with
  | inl b =>
      cases b with
      | false => rfl
      | true => exact (hxj (interior_subset hx)).elim
  | inr i =>
      have hneg : x ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) := by
        rw [← (P i).collar_retained_inter]
        exact ⟨hxj, hx⟩
      exact congrArg (fun c => eventGraphVertexClass F T hT P (Sum.inl c))
        ((P i).negative_retained_component_eq ⟨x, hx⟩ hneg).symm

theorem eventPrePatchLabel_on_discarded (j : Bool ⊕ Fin (F.event T hT).cap_count)
    (x : (F.slice (F.event T hT).tMinus).carrier) (hxj : x ∈ eventPrePatch F T hT P j)
    (hx : x ∈ eventDiscardedOpen F T hT) :
    eventPrePatchLabel F T hT P j ⟨x, hxj⟩ = discardedGraphLabel F T hT P ⟨x, hx⟩ := by
  cases j with
  | inl b =>
      cases b with
      | false => exact (hx (interior_subset hxj)).elim
      | true => rfl
  | inr i =>
      have hpos : x ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
        rw [← (P i).collar_discarded_inter]
        exact ⟨hxj, hx⟩
      exact (eventGraphVertexClass_edge F T hT P i).trans
        (congrArg (fun c => eventGraphVertexClass F T hT P (Sum.inr c))
          ((P i).positive_discarded_component_eq ⟨x, hx⟩ hpos).symm)

theorem eventPrePatchLabel_agree (j k : Bool ⊕ Fin (F.event T hT).cap_count)
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hxj : x ∈ eventPrePatch F T hT P j) (hxk : x ∈ eventPrePatch F T hT P k) :
    eventPrePatchLabel F T hT P j ⟨x, hxj⟩ =
      eventPrePatchLabel F T hT P k ⟨x, hxk⟩ := by
  by_cases hr : x ∈ eventRetainedInteriorOpen F T hT
  · rw [eventPrePatchLabel_on_retained F T hT P j x hxj hr,
      eventPrePatchLabel_on_retained F T hT P k x hxk hr]
  by_cases hd : x ∈ eventDiscardedOpen F T hT
  · rw [eventPrePatchLabel_on_discarded F T hT P j x hxj hd,
      eventPrePatchLabel_on_discarded F T hT P k x hxk hd]
  cases j with
  | inl b => cases b <;> first | exact (hr hxj).elim | exact (hd hxj).elim
  | inr i =>
      cases k with
      | inl b => cases b <;> first | exact (hr hxk).elim | exact (hd hxk).elim
      | inr j =>
          by_cases hij : i = j
          · subst j
            rfl
          · exact (Set.disjoint_left.mp ((P i).collars_disjoint (P j) hij) hxj hxk).elim

theorem eventPrePatch_cover (x : (F.slice (F.event T hT).tMinus).carrier) :
    ∃ j, (eventPrePatch F T hT P j : Set (F.slice (F.event T hT).tMinus).carrier) ∈ 𝓝 x := by
  by_cases hr : x ∈ eventRetainedInteriorOpen F T hT
  · exact ⟨Sum.inl false, (eventRetainedInteriorOpen F T hT).isOpen.mem_nhds hr⟩
  by_cases hd : x ∈ eventDiscardedOpen F T hT
  · exact ⟨Sum.inl true, (eventDiscardedOpen F T hT).isOpen.mem_nhds hd⟩
  have hret : x ∈ (F.event T hT).retained_pre := by
    by_contra h
    exact hd h
  have hf : x ∈ frontier (F.event T hT).retained_pre := by
    rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    exact ⟨hret, hr⟩
  rw [(F.event T hT).pre_boundary] at hf
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hf
  rw [← (P i).collar_central] at hi
  refine ⟨Sum.inr i, (P i).collarChart.open_target.mem_nhds ?_⟩
  apply Set.image_mono _ hi
  rintro ⟨z, s⟩ ⟨hz, hs⟩
  have hs0 : s = 0 := hs
  subst s
  exact ⟨hz, by norm_num⟩

noncomputable def preEventGraphLabel :
    C((F.slice (F.event T hT).tMinus).carrier, EventGraphComponent F T hT P) :=
  ContinuousMap.liftCover (fun j => eventPrePatch F T hT P j)
    (eventPrePatchLabel F T hT P) (eventPrePatchLabel_agree F T hT P)
    (eventPrePatch_cover F T hT P)

theorem preEventGraphLabel_patch (j : Bool ⊕ Fin (F.event T hT).cap_count)
    (x : eventPrePatch F T hT P j) :
    preEventGraphLabel F T hT P x.val = eventPrePatchLabel F T hT P j x :=
  ContinuousMap.liftCover_coe
    (S := fun j : Bool ⊕ Fin (F.event T hT).cap_count =>
      (eventPrePatch F T hT P j : Set (F.slice (F.event T hT).tMinus).carrier))
    (φ := eventPrePatchLabel F T hT P) (hφ := eventPrePatchLabel_agree F T hT P)
    (hS := eventPrePatch_cover F T hT P) (i := j) x

theorem preEventGraphLabel_retained (x : eventRetainedInteriorOpen F T hT) :
    preEventGraphLabel F T hT P x.val =
      eventGraphVertexClass F T hT P (Sum.inl (ConnectedComponents.mk x)) :=
  preEventGraphLabel_patch F T hT P (Sum.inl false) x

theorem preEventGraphLabel_discarded (x : eventDiscardedOpen F T hT) :
    preEventGraphLabel F T hT P x.val =
      eventGraphVertexClass F T hT P (Sum.inr (ConnectedComponents.mk x)) :=
  preEventGraphLabel_patch F T hT P (Sum.inl true) x

theorem preEventGraphLabel_collar (i : Fin (F.event T hT).cap_count)
    (x : (F.slice (F.event T hT).tMinus).carrier)
    (hx : x ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
    preEventGraphLabel F T hT P x = eventGraphVertexClass F T hT P
      (Sum.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) :=
  preEventGraphLabel_patch F T hT P (Sum.inr i) ⟨x, hx⟩

end PoincareConjecture.M38
