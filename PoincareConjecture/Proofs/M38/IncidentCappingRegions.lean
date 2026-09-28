import PoincareConjecture.Proofs.M38.CappingRegions
import PoincareConjecture.Proofs.M38.CappingComponents
import PoincareConjecture.Proofs.M38.ComponentBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance incidentCappedChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P

local instance incidentCappedManifold :
    IsManifold (𝓡 3) ∞ (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedSpace_isManifold F T hT P

noncomputable def incidentOldCarrier : GeneralizedSliceCarrier.{u} :=
  openCarrier (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT)

theorem cappedCapBall_image_disjoint (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j) :
    Disjoint ((cappedCapBall F T hT P i).map '' Metric.ball 0 2)
      ((cappedCapBall F T hT P j).map '' Metric.ball 0 2) := by
  apply (cappedCapPatch_disjoint F T hT P i j hij).mono
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, (cappedCapBall_map F T hT P i ⟨z, hz⟩).symm⟩
  · rintro y ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, (cappedCapBall_map F T hT P j ⟨z, hz⟩).symm⟩

variable (x : eventDiscardedOpen F T hT)

def incidentCapIndex :=
  {i : Fin (F.event T hT).cap_count //
    ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x}

instance incidentCapIndex_finite : Finite (incidentCapIndex F T hT P x) :=
  inferInstanceAs (Finite {i : Fin (F.event T hT).cap_count //
    ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x})

theorem cappedCapBall_mem_component_iff (i : Fin (F.event T hT).cap_count)
    {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
    (cappedCapBall F T hT P i).map z ∈
        connectedComponent (cappedOldInclusion F T hT P x) ↔
      ConnectedComponents.mk (P i).attachmentPoint = ConnectedComponents.mk x := by
  rw [cappedCapBall_map F T hT P i ⟨z, hz⟩]
  let H := cappedComponentsHomeomorph F T hT P
  have hpatch := cappedCapPatch_component F T hT P i ⟨z, hz⟩
  constructor
  · intro h
    apply H.injective
    rw [cappedComponentsHomeomorph_apply, cappedComponentsHomeomorph_apply]
    exact hpatch.symm.trans (ConnectedComponents.coe_eq_coe'.mpr h)
  · intro h
    apply ConnectedComponents.coe_eq_coe'.mp
    exact hpatch.trans (by
      rw [← cappedComponentsHomeomorph_apply, ← cappedComponentsHomeomorph_apply]
      exact congrArg H h)

theorem incidentCapBall_center_mem (i : incidentCapIndex F T hT P x) :
    (cappedCapBall F T hT P i.val).map 0 ∈
      connectedComponent (cappedOldInclusion F T hT P x) :=
  (cappedCapBall_mem_component_iff F T hT P x i.val (by simp)).mpr i.property

noncomputable def incidentCapBall (i : incidentCapIndex F T hT P x) :
    SurgeryBallEmbedding (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)) :=
  componentBall (cappedCapBall F T hT P i.val) (cappedOldInclusion F T hT P x)
    (incidentCapBall_center_mem F T hT P x i)

theorem incidentCapBall_map_val (i : incidentCapIndex F T hT P x)
    {z : StandardCapSpace} (hz : z ∈ Metric.ball 0 2) :
    ((incidentCapBall F T hT P x i).map z).val = (cappedCapBall F T hT P i.val).map z :=
  componentBall_map_val _ _ _ hz

theorem incidentCapBall_image_disjoint (i j : incidentCapIndex F T hT P x) (hij : i ≠ j) :
    Disjoint ((incidentCapBall F T hT P x i).map '' Metric.ball 0 2)
      ((incidentCapBall F T hT P x j).map '' Metric.ball 0 2) := by
  apply disjoint_left.mpr
  rintro y ⟨z, hz, rfl⟩ ⟨w, hw, hwy⟩
  have heq := congrArg Subtype.val hwy
  rw [incidentCapBall_map_val F T hT P x j hw,
    incidentCapBall_map_val F T hT P x i hz] at heq
  exact disjoint_left.mp (cappedCapBall_image_disjoint F T hT P i.val j.val
    (fun h => hij (Subtype.ext h))) ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩

theorem incidentCapBall_union_iff
    (q : (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)).carrier) :
    q ∈ ⋃ i, (incidentCapBall F T hT P x i).closedBall ↔
      q.val ∈ ⋃ i, (cappedCapBall F T hT P i).closedBall := by
  constructor
  · intro hq
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨i.val, z, hz,
      (incidentCapBall_map_val F T hT P x i
        (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz)).symm⟩
  · intro hq
    obtain ⟨i, z, hz, hzq⟩ := mem_iUnion.mp hq
    have hz2 := Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz
    have hi := (cappedCapBall_mem_component_iff F T hT P x i hz2).mp
      (hzq.symm ▸ q.property)
    refine mem_iUnion.mpr ⟨⟨i, hi⟩, z, hz, ?_⟩
    apply Subtype.ext
    exact (incidentCapBall_map_val F T hT P x ⟨i, hi⟩ hz2).trans hzq

theorem incidentOldInverse_mem
    (q : (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)).carrier)
    (hq : q ∈ (⋃ i, (incidentCapBall F T hT P x i).closedBall)ᶜ) :
    cappedOldInverse F T hT P q.val ∈ connectedComponent x := by
  have hqold : q.val ∈ range (cappedOldInclusion F T hT P) := by
    rw [cappedOldInclusion_range]
    exact fun h => hq ((incidentCapBall_union_iff F T hT P x q).mpr h)
  have hcomponent : cappedOldInclusion F T hT P
      (cappedOldInverse F T hT P q.val) ∈
        connectedComponent (cappedOldInclusion F T hT P x) := by
    rw [cappedOldInverse_right F T hT P hqold]
    exact q.property
  rw [← cappedOldInclusion_preimage_component F T hT P x]
  exact hcomponent

noncomputable def incidentOldInclusion
    (y : (componentCarrier (incidentOldCarrier F T hT) x).carrier) :
    (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)).carrier :=
  ⟨cappedOldInclusion F T hT P y.val,
    (cappedOldInclusion_openEmbedding F T hT P).continuous.image_connectedComponent_subset x
      (mem_image_of_mem _ y.property)⟩

theorem incidentOldInclusion_range :
    range (incidentOldInclusion F T hT P x) =
      (⋃ i, (incidentCapBall F T hT P x i).closedBall)ᶜ := by
  ext q
  constructor
  · rintro ⟨y, rfl⟩ hcap
    have hcap' := (incidentCapBall_union_iff F T hT P x _).mp hcap
    have hold : cappedOldInclusion F T hT P y.val ∈
        (⋃ i, (cappedCapBall F T hT P i).closedBall)ᶜ := by
      rw [← cappedOldInclusion_range]
      exact mem_range_self _
    change cappedOldInclusion F T hT P y.val ∈
      ⋃ i, (cappedCapBall F T hT P i).closedBall at hcap'
    exact hold hcap'
  · intro hq
    refine ⟨⟨cappedOldInverse F T hT P q.val,
      incidentOldInverse_mem F T hT P x q hq⟩, ?_⟩
    apply Subtype.ext
    change cappedOldInclusion F T hT P
      (cappedOldInverse F T hT P q.val) = q.val
    apply cappedOldInverse_right
    rw [cappedOldInclusion_range]
    exact fun h => hq ((incidentCapBall_union_iff F T hT P x q).mpr h)

noncomputable def incidentOldRegionEquivalence :
    SurgeryRegionEquivalence
      (componentCarrier (incidentOldCarrier F T hT) x)
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)) univ
      (⋃ i, (incidentCapBall F T hT P x i).closedBall)ᶜ := by
  let E := componentRegionEquivalence (incidentOldCarrier F T hT) x
  let inverse := fun q : (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)).carrier =>
    E.inverse (cappedOldInverse F T hT P q.val)
  have hleft (y : (componentCarrier (incidentOldCarrier F T hT) x).carrier) :
      inverse (incidentOldInclusion F T hT P x y) = y := by
    dsimp only [inverse, incidentOldInclusion]
    rw [cappedOldInverse_apply]
    exact E.left_inverse (mem_univ _)
  have hright (q : (componentCarrier (cappedDiscardedCarrier F T hT P)
      (cappedOldInclusion F T hT P x)).carrier)
      (hq : q ∈ (⋃ i, (incidentCapBall F T hT P x i).closedBall)ᶜ) :
      incidentOldInclusion F T hT P x (inverse q) = q := by
    apply Subtype.ext
    change cappedOldInclusion F T hT P
      (E.map (E.inverse (cappedOldInverse F T hT P q.val))) = q.val
    rw [E.right_inverse (incidentOldInverse_mem F T hT P x q hq)]
    apply cappedOldInverse_right
    rw [cappedOldInclusion_range]
    exact fun h => hq ((incidentCapBall_union_iff F T hT P x q).mpr h)
  refine {
    map := incidentOldInclusion F T hT P x
    inverse := inverse
    map_image := by rw [image_univ, incidentOldInclusion_range]
    inverse_image := ?_
    left_inverse := fun y _ => hleft y
    right_inverse := hright
    map_smooth := ?_
    inverse_smooth := ?_ }
  · rw [← incidentOldInclusion_range]
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨incidentOldInclusion F T hT P x y, mem_range_self _, hleft y⟩
  · apply ContMDiff.contMDiffOn
    apply (ContMDiff.subtypeVal_comp_iff
      (componentOpen (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)) _).mp
    exact (cappedOldInclusion_smooth F T hT P).comp
      (contMDiff_subtype_val (U := componentOpen (incidentOldCarrier F T hT) x))
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (E.inverse ∘ fun q : (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)).carrier =>
        cappedOldInverse F T hT P q.val) _
    apply E.inverse_smooth.comp ?_
      (fun q hq => incidentOldInverse_mem F T hT P x q hq)
    apply (cappedOldRegionEquivalence F T hT P).inverse_smooth.comp
      (contMDiff_subtype_val (U := componentOpen (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x))).contMDiffOn
    intro q hq
    exact fun h => hq ((incidentCapBall_union_iff F T hT P x q).mpr h)

noncomputable def incidentAttachmentPoint (i : incidentCapIndex F T hT P x)
    (z : capDoubleBall) (hz : 1 < ‖z.val‖) :
      (componentCarrier (incidentOldCarrier F T hT) x).carrier := by
  have hzsource : z ∈ (P i.val).attachmentChart.source := by
    rw [(P i.val).attachmentChart_source]
    exact hz
  exact ⟨(P i.val).attachmentChart z, ConnectedComponents.coe_eq_coe'.mp
    (((P i.val).attachment_component_eq ((P i.val).attachmentChart.map_source hzsource)).trans
      i.property)⟩

theorem incidentOldRegionEquivalence_attachment (i : incidentCapIndex F T hT P x)
    (z : capDoubleBall) (hz : 1 < ‖z.val‖) :
    (incidentOldRegionEquivalence F T hT P x).map
        (incidentAttachmentPoint F T hT P x i z hz) =
      (incidentCapBall F T hT P x i).map z.val := by
  apply Subtype.ext
  rw [incidentCapBall_map_val F T hT P x i z.property,
    cappedCapBall_attachment F T hT P i.val z hz]
  rfl

end PoincareConjecture.M38
