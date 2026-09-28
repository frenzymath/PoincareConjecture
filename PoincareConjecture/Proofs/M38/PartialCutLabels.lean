import PoincareConjecture.Proofs.M38.CutOldLabels
import PoincareConjecture.Proofs.M38.PartialCutBalls









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  {D : Type v} [TopologicalSpace D] (label : EventCutVertex F T hT → D)
  (hagrees : ∀ i, i ∉ S →
    label (.inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)) =
      label (.inr (ConnectedComponents.mk (P i).attachmentPoint)))


noncomputable def cutSideVertex (i : Fin (F.event T hT).cap_count) : Bool → EventCutVertex F T hT
  | false => .inl (ConnectedComponents.mk (P i).retainedAttachmentPoint)
  | true => .inr (ConnectedComponents.mk (P i).attachmentPoint)


theorem cutOldLabel_attachment (a : S × Bool) (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    cutOldLabel F T hT P S label hagrees (cutAttachmentChart F T hT P S a x) =
      label (cutSideVertex F T hT P a.1.val a.2) := by
  let y := cutAttachmentChart F T hT P S a x
  have hy : y.val ∈ ((P a.1.val).cutAnnularChart a.2).target := by
    have hsource : x ∈ (cutAttachmentChart F T hT P S a).source := by
      rwa [cutAttachmentChart_source]
    have h := (cutAttachmentChart F T hT P S a).map_source hsource
    rwa [cutAttachmentChart_target] at h
  rcases a with ⟨i, positive⟩
  cases positive with
  | false =>
      have hneg : y.val ∈ (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 0) := by
        obtain ⟨⟨z, s⟩, hs, hmap⟩ := hy
        refine ⟨(z, -s), ⟨Set.mem_univ _, by linarith [hs.2.2], by linarith [hs.2.1]⟩, ?_⟩
        exact hmap
      have hr : y.val ∈ eventRetainedInteriorOpen F T hT := (P i.val).negative_interior hneg
      rw [cutOldLabel_retained F T hT P S label hagrees y hr]
      exact congrArg (fun c => label (.inl c))
        ((P i.val).negative_retained_component_eq ⟨y.val, hr⟩ hneg)
  | true =>
      have hpos : y.val ∈ (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
        obtain ⟨z, hz, hmap⟩ := hy
        exact ⟨z, hz, hmap⟩
      have hd : y.val ∈ eventDiscardedOpen F T hT :=
        fun h => Set.disjoint_left.mp (P i.val).positive_disjoint hpos h
      rw [cutOldLabel_discarded F T hT P S label hagrees y hd]
      exact congrArg (fun c => label (.inr c))
        ((P i.val).positive_discarded_component_eq ⟨y.val, hd⟩ hpos)


noncomputable def partialCutPatchLabel :
    (j : PartialCappingIndex F T hT P S) → partialCappingDomain F T hT P S j → D
  | .inl y, x => cutOldLabel F T hT P S label hagrees
      (partialCappingMap F T hT P S (.inl y) x)
  | .inr a, _ => label (cutSideVertex F T hT P a.1.val a.2)


theorem partialCutPatchLabel_source (j : PartialCappingIndex F T hT P S)
    {x : partialCappingDomain F T hT P S j}
    (hx : x ∈ (partialCappingMap F T hT P S j).source) :
    partialCutPatchLabel F T hT P S label hagrees j x =
      cutOldLabel F T hT P S label hagrees (partialCappingMap F T hT P S j x) := by
  cases j with
  | inl y => rfl
  | inr a =>
      exact (cutOldLabel_attachment F T hT P S label hagrees a x
        (by change x ∈ (cutAttachmentChart F T hT P S a).source at hx
            rwa [cutAttachmentChart_source] at hx)).symm


theorem partialCutPatchLabel_rel
    (a b : Sigma (fun j => partialCappingDomain F T hT P S j))
    (hab : (partialCappingOverlap F T hT P S).Rel a b) :
    partialCutPatchLabel F T hT P S label hagrees a.1 a.2 =
      partialCutPatchLabel F T hT P S label hagrees b.1 b.2 := by
  rcases a with ⟨j, x⟩
  rcases b with ⟨k, y⟩
  by_cases hjk : j = k
  · subst k
    have hxy : x = y := by
      simpa only [Poincare.Gluing.OverlapSystem.Rel, partialCappingOverlap,
        cappingOverlap, cappingTransition_self, OpenPartialHomeomorph.refl_apply, id_eq] using hab.2
    exact congrArg (partialCutPatchLabel F T hT P S label hagrees j) hxy
  · have h := (cappingTransition_graph (partialCappingMap F T hT P S) hjk x y).mp hab
    rw [partialCutPatchLabel_source F T hT P S label hagrees j h.1,
      partialCutPatchLabel_source F T hT P S label hagrees k h.2.1, h.2.2]


noncomputable def partialCutLabel : PartialCappedSpace F T hT P S → D :=
  Quotient.lift (fun a => partialCutPatchLabel F T hT P S label hagrees a.1 a.2)
    (partialCutPatchLabel_rel F T hT P S label hagrees)


theorem partialCutLabel_patch (j : PartialCappingIndex F T hT P S)
    (x : partialCappingDomain F T hT P S j) :
    partialCutLabel F T hT P S label hagrees (partialCappingInclude F T hT P S j x) =
      partialCutPatchLabel F T hT P S label hagrees j x := rfl


theorem partialCutPatchLabel_continuous (j : PartialCappingIndex F T hT P S) :
    Continuous (partialCutPatchLabel F T hT P S label hagrees j) := by
  cases j with
  | inl y =>
      exact (cutOldLabel F T hT P S label hagrees).continuous.comp
        (partialCappingMap_old_openEmbedding F T hT P S y).continuous
  | inr a => exact continuous_const


theorem partialCutLabel_continuous : Continuous (partialCutLabel F T hT P S label hagrees) :=
  (continuous_sigma (partialCutPatchLabel_continuous F T hT P S label hagrees)).quotient_lift
    (partialCutPatchLabel_rel F T hT P S label hagrees)


theorem partialCutLabel_ball (a : S × Bool) (x : capDoubleBall) :
    partialCutLabel F T hT P S label hagrees ((partialCapBall F T hT P S a).map x.val) =
      label (cutSideVertex F T hT P a.1.val a.2) := by
  rw [partialCapBall_map, partialCutLabel_patch]
  rfl

include hagrees in

theorem partialCut_centers_separated [TotallyDisconnectedSpace D] (a b : S × Bool)
    (hne : label (cutSideVertex F T hT P a.1.val a.2) ≠
      label (cutSideVertex F T hT P b.1.val b.2)) :
    ConnectedComponents.mk ((partialCapBall F T hT P S a).map 0) ≠
      ConnectedComponents.mk ((partialCapBall F T hT P S b).map 0) := by
  intro h
  have heq := congrArg (partialCutLabel_continuous F T hT P S label hagrees).connectedComponentsLift h
  change partialCutLabel F T hT P S label hagrees ((partialCapBall F T hT P S a).map 0) =
    partialCutLabel F T hT P S label hagrees ((partialCapBall F T hT P S b).map 0) at heq
  let z : capDoubleBall := ⟨0, by simp [capDoubleBall]⟩
  exact hne ((partialCutLabel_ball F T hT P S label hagrees a z).symm.trans
    (heq.trans (partialCutLabel_ball F T hT P S label hagrees b z)))

end PoincareConjecture.M38
