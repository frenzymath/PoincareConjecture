import PoincareConjecture.Proofs.M38.RetainedComponentLabels
import PoincareConjecture.Proofs.M38.Components









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)



theorem post_cap_patch_component (i : Fin (F.event T hT).cap_count)
    (x : (F.slice T).carrier) (hx : x ∈ (P i).ball.map '' Metric.ball 0 2) :
    ConnectedComponents.mk x = ConnectedComponents.mk (P i).retainedAnnularPoint.val := by
  let : ConnectedSpace (Metric.ball (0 : StandardCapSpace) 2) := capDoubleBall_connected
  have hconnected : IsConnected ((P i).ball.map '' Metric.ball (0 : StandardCapSpace) 2) := by
    have h := isConnected_range (P i).ball.open_embedding.continuous
    change IsConnected (Set.range ((P i).ball.map ∘
      (Subtype.val : Metric.ball (0 : StandardCapSpace) 2 → StandardCapSpace))) at h
    simpa only [Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h
  exact ConnectedComponents.coe_eq_coe'.mpr
    (hconnected.subset_connectedComponent (P i).retainedAnnularPoint_mem hx)




noncomputable def capComplementComponentsHomeomorph :
    ConnectedComponents (eventCapComplementOpen F T hT) ≃ₜ
      ConnectedComponents (F.slice T).carrier where
  toFun := (continuous_subtype_val : Continuous
    (Subtype.val : eventCapComplementOpen F T hT → (F.slice T).carrier)).connectedComponentsMap
  invFun := (postRetainedComponentLabel F T hT P).continuous.connectedComponentsLift
  left_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact postRetainedComponentLabel_old F T hT P x
  right_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change (continuous_subtype_val : Continuous
      (Subtype.val : eventCapComplementOpen F T hT → (F.slice T).carrier)).connectedComponentsMap
        (postRetainedComponentLabel F T hT P x) = ConnectedComponents.mk x
    by_cases hx : x ∈ eventCapComplementOpen F T hT
    · rw [postRetainedComponentLabel_old F T hT P ⟨x, hx⟩]
      rfl
    · have hcaps : x ∈ ⋃ i, ((F.event T hT).caps i).carrier := by
        by_contra h
        exact hx h
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcaps
      rw [← (P i).ball_closedBall] at hi
      have hpatch : x ∈ (P i).ball.map '' Metric.ball (0 : StandardCapSpace) 2 :=
        Set.image_mono (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) hi
      rw [postRetainedComponentLabel_cap F T hT P i x hpatch]
      exact (post_cap_patch_component F T hT P i x hpatch).symm
  continuous_toFun := (continuous_subtype_val : Continuous
    (Subtype.val : eventCapComplementOpen F T hT →
      (F.slice T).carrier)).connectedComponentsMap_continuous
  continuous_invFun :=
    (postRetainedComponentLabel F T hT P).continuous.connectedComponentsLift_continuous


theorem capComplementComponentsHomeomorph_apply (x : eventCapComplementOpen F T hT) :
    capComplementComponentsHomeomorph F T hT P (ConnectedComponents.mk x) =
      ConnectedComponents.mk x.val := rfl


theorem capComplementComponentsHomeomorph_symm_apply (x : (F.slice T).carrier) :
    (capComplementComponentsHomeomorph F T hT P).symm (ConnectedComponents.mk x) =
      postRetainedComponentLabel F T hT P x := rfl

include P in


theorem capComplement_preimage_component (x : eventCapComplementOpen F T hT) :
    (Subtype.val : eventCapComplementOpen F T hT → (F.slice T).carrier) ⁻¹'
      connectedComponent x.val = connectedComponent x := by
  ext y
  constructor
  · intro hy
    apply ConnectedComponents.coe_eq_coe'.mp
    apply (capComplementComponentsHomeomorph F T hT P).injective
    exact ConnectedComponents.coe_eq_coe'.mpr hy
  · intro hy
    apply ConnectedComponents.coe_eq_coe'.mp
    exact congrArg (capComplementComponentsHomeomorph F T hT P)
      (ConnectedComponents.coe_eq_coe'.mpr hy)


def eventRetainedInteriorOpen :
    TopologicalSpace.Opens (F.slice (F.event T hT).tMinus).carrier :=
  ⟨interior (F.event T hT).retained_pre, isOpen_interior⟩



def retentionInteriorHomeomorph :
    eventRetainedInteriorOpen F T hT ≃ₜ eventCapComplementOpen F T hT where
  toFun := fun x => ⟨(F.event T hT).retention.map x.val,
    (retention_interior_image F T hT).subset (Set.mem_image_of_mem _ x.property)⟩
  invFun := fun x => ⟨(F.event T hT).retention.inverse x.val,
    (retention_inverse_cap_complement_image F T hT).subset
      (Set.mem_image_of_mem _ x.property)⟩
  left_inv := fun x => Subtype.ext ((retentionInteriorEquivalence F T hT).left_inverse x.property)
  right_inv := fun x => Subtype.ext ((retentionInteriorEquivalence F T hT).right_inverse x.property)
  continuous_toFun :=
    (retentionInteriorEquivalence F T hT).map_smooth.continuousOn.domRestrict.subtype_mk _
  continuous_invFun :=
    (retentionInteriorEquivalence F T hT).inverse_smooth.continuousOn.domRestrict.subtype_mk _


noncomputable def retentionInteriorComponentsHomeomorph :
    ConnectedComponents (eventRetainedInteriorOpen F T hT) ≃ₜ
      ConnectedComponents (eventCapComplementOpen F T hT) where
  toFun := (retentionInteriorHomeomorph F T hT).continuous.connectedComponentsMap
  invFun := (retentionInteriorHomeomorph F T hT).symm.continuous.connectedComponentsMap
  left_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg ConnectedComponents.mk ((retentionInteriorHomeomorph F T hT).symm_apply_apply x)
  right_inv := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact congrArg ConnectedComponents.mk ((retentionInteriorHomeomorph F T hT).apply_symm_apply x)
  continuous_toFun :=
    (retentionInteriorHomeomorph F T hT).continuous.connectedComponentsMap_continuous
  continuous_invFun :=
    (retentionInteriorHomeomorph F T hT).symm.continuous.connectedComponentsMap_continuous



noncomputable def retainedComponentsHomeomorph :
    ConnectedComponents (eventRetainedInteriorOpen F T hT) ≃ₜ
      ConnectedComponents (F.slice T).carrier :=
  (retentionInteriorComponentsHomeomorph F T hT).trans (capComplementComponentsHomeomorph F T hT P)


theorem retainedComponentsHomeomorph_apply (x : eventRetainedInteriorOpen F T hT) :
    retainedComponentsHomeomorph F T hT P (ConnectedComponents.mk x) =
      ConnectedComponents.mk ((F.event T hT).retention.map x.val) := rfl

include P in


theorem eventRetainedInterior_finite_components :
    Finite (ConnectedComponents (eventRetainedInteriorOpen F T hT)) := by
  let : Finite (ConnectedComponents (F.slice T).carrier) :=
    finite_components (F.slice T) (F.slices_compact T (F.surgery_times_subset hT))
  exact Finite.of_injective (retainedComponentsHomeomorph F T hT P)
    (retainedComponentsHomeomorph F T hT P).injective

end PoincareConjecture.M38
