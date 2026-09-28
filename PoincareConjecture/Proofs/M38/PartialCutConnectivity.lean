import PoincareConjecture.Proofs.M38.PartialCutLabels
import PoincareConjecture.Proofs.M38.UncutCollar
import PoincareConjecture.Proofs.M38.ComponentBalls
import PoincareConjecture.Proofs.M38.FullCutSides
import PoincareConjecture.Proofs.M38.SuccessiveCutDomains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

theorem retained_subset_partialCut :
    eventRetainedInteriorOpen F T hT ≤ eventCutOpen F T hT P S :=
  (retained_subset_fullCut F T hT P).trans
    (eventCutOpen_antitone F T hT P S Set.univ (Set.subset_univ _))

theorem discarded_subset_partialCut :
    eventDiscardedOpen F T hT ≤ eventCutOpen F T hT P S :=
  (discarded_subset_fullCut F T hT P).trans
    (eventCutOpen_antitone F T hT P S Set.univ (Set.subset_univ _))

noncomputable def partialCutRetained :
    eventRetainedInteriorOpen F T hT → (partialCappedCarrier F T hT P S).carrier :=
  partialOldInclusion F T hT P S ∘ Set.inclusion (retained_subset_partialCut F T hT P S)

noncomputable def partialCutDiscarded :
    eventDiscardedOpen F T hT → (partialCappedCarrier F T hT P S).carrier :=
  partialOldInclusion F T hT P S ∘ Set.inclusion (discarded_subset_partialCut F T hT P S)

theorem partialCutRetained_continuous : Continuous (partialCutRetained F T hT P S) :=
  (partialOldInclusion_openEmbedding F T hT P S).continuous.comp
    (continuous_inclusion (retained_subset_partialCut F T hT P S))

theorem partialCutDiscarded_continuous : Continuous (partialCutDiscarded F T hT P S) :=
  (partialOldInclusion_openEmbedding F T hT P S).continuous.comp
    (continuous_inclusion (discarded_subset_partialCut F T hT P S))

noncomputable def partialCutVertexComponent :
    EventCutVertex F T hT → ConnectedComponents (partialCappedCarrier F T hT P S).carrier :=
  Sum.elim (partialCutRetained_continuous F T hT P S).connectedComponentsMap
    (partialCutDiscarded_continuous F T hT P S).connectedComponentsMap

theorem partialCutVertexComponent_retained (x : eventRetainedInteriorOpen F T hT) :
    partialCutVertexComponent F T hT P S (.inl (ConnectedComponents.mk x)) =
      ConnectedComponents.mk (partialCutRetained F T hT P S x) := rfl

theorem partialCutVertexComponent_discarded (x : eventDiscardedOpen F T hT) :
    partialCutVertexComponent F T hT P S (.inr (ConnectedComponents.mk x)) =
      ConnectedComponents.mk (partialCutDiscarded F T hT P S x) := rfl

theorem partialCut_collar_component_eq (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)
    (x y : eventCutOpen F T hT P S)
    (hx : x.val ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
    (hy : y.val ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
    ConnectedComponents.mk (partialOldInclusion F T hT P S x) =
      ConnectedComponents.mk (partialOldInclusion F T hT P S y) := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  have hc : IsConnected (uncutCollar F T hT P S i hi ''
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
    apply (isConnected_univ.prod (isConnected_Ioo (by norm_num))).image
    rw [← uncutCollar_source F T hT P S i hi]
    exact (uncutCollar F T hT P S i hi).toOpenPartialHomeomorph.continuousOn_toFun
  have hmem (z : eventCutOpen F T hT P S)
      (hz : z.val ∈ (P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
      partialOldInclusion F T hT P S z ∈ uncutCollar F T hT P S i hi ''
        (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨w, hw, ?_⟩
    rw [uncutCollar_apply]
    exact congrArg (partialOldInclusion F T hT P S)
      (Subtype.ext ((uncutCollarOldChart_apply F T hT P S i hi w hw).trans hwz))
  exact ConnectedComponents.coe_eq_coe'.mpr (hc.subset_connectedComponent (hmem y hy) (hmem x hx))

theorem partialCutVertexComponent_uncut (i : Fin (F.event T hT).cap_count) (hi : i ∉ S) :
    partialCutVertexComponent F T hT P S (cutSideVertex F T hT P i false) =
      partialCutVertexComponent F T hT P S (cutSideVertex F T hT P i true) := by
  apply partialCut_collar_component_eq F T hT P S i hi
  · apply Set.image_mono _ (P i).retainedAttachmentPoint_negative
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.trans zero_lt_one⟩
  · exact Set.image_mono positive_collar_subset (P i).attachmentPoint_positive

theorem partialCut_attachment_component (a : S × Bool) (x : capDoubleBall)
    (hx : 1 < ‖x.val‖) :
    ConnectedComponents.mk
        (partialOldInclusion F T hT P S (cutAttachmentChart F T hT P S a x)) =
      partialCutVertexComponent F T hT P S (cutSideVertex F T hT P a.1.val a.2) := by
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
        exact ⟨(z, -s), ⟨Set.mem_univ _, by linarith [hs.2.2], by linarith [hs.2.1]⟩, hmap⟩
      have hr : y.val ∈ eventRetainedInteriorOpen F T hT := (P i.val).negative_interior hneg
      exact congrArg (fun c => partialCutVertexComponent F T hT P S (.inl c))
        ((P i.val).negative_retained_component_eq ⟨y.val, hr⟩ hneg)
  | true =>
      have hpos : y.val ∈ (P i.val).collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
        obtain ⟨z, hz, hmap⟩ := hy
        exact ⟨z, hz, hmap⟩
      have hd : y.val ∈ eventDiscardedOpen F T hT :=
        fun h => Set.disjoint_left.mp (P i.val).positive_disjoint hpos h
      exact congrArg (fun c => partialCutVertexComponent F T hT P S (.inr c))
        ((P i.val).positive_discarded_component_eq ⟨y.val, hd⟩ hpos)

theorem partialCut_ball_center_component (a : S × Bool) :
    ConnectedComponents.mk ((partialCapBall F T hT P S a).map 0) =
      partialCutVertexComponent F T hT P S (cutSideVertex F T hT P a.1.val a.2) := by
  let z := capUnitDirection 0
  have hz : ‖z.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  let x : capDoubleBall := ⟨(3 / 2 : ℝ) • z.val, by
    change dist ((3 / 2 : ℝ) • z.val) 0 < 2
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), hz]
    norm_num⟩
  have hx : 1 < ‖x.val‖ := by
    change 1 < ‖(3 / 2 : ℝ) • z.val‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), hz]
    norm_num
  have hc : ConnectedComponents.mk ((partialCapBall F T hT P S a).map x.val) =
      ConnectedComponents.mk ((partialCapBall F T hT P S a).map 0) :=
    ConnectedComponents.coe_eq_coe'.mpr
      (surgeryBall_image_subset_center_component (partialCapBall F T hT P S a)
        ⟨x.val, x.property, rfl⟩)
  rw [← hc, partialCapBall_attachment F T hT P S a x hx]
  exact partialCut_attachment_component F T hT P S a x hx

end PoincareConjecture.M38
