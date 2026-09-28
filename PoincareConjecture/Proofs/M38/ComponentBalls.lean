import PoincareConjecture.Proofs.M38.RetainedComponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

theorem surgeryBall_image_connected :
    IsConnected (B.map '' Metric.ball (0 : StandardCapSpace) 2) := by
  let : ConnectedSpace (Metric.ball (0 : StandardCapSpace) 2) := capDoubleBall_connected
  have h := isConnected_range B.open_embedding.continuous
  change IsConnected (Set.range (B.map ∘
    (Subtype.val : Metric.ball (0 : StandardCapSpace) 2 → StandardCapSpace))) at h
  simpa only [Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h

theorem surgeryBall_image_subset_center_component :
    B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ connectedComponent (B.map 0) :=
  (surgeryBall_image_connected B).subset_connectedComponent ⟨0, by simp, rfl⟩

theorem surgeryBall_image_subset_component (x : A.carrier)
    (hx : B.map 0 ∈ connectedComponent x) :
    B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ connectedComponent x := by
  simpa only [connectedComponent_eq hx] using surgeryBall_image_subset_center_component B

noncomputable def componentBall (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x) :
    SurgeryBallEmbedding (componentCarrier A x) := by
  let E := componentRegionEquivalence A x
  have hmap (z : StandardCapSpace) (hz : z ∈ Metric.ball (0 : StandardCapSpace) 2) :
      E.map (E.inverse (B.map z)) = B.map z :=
    E.right_inverse (surgeryBall_image_subset_component B x hx ⟨z, hz, rfl⟩)
  refine {
    map := E.inverse ∘ B.map
    inverse := B.inverse ∘ E.map
    map_smooth := E.inverse_smooth.comp B.map_smooth
      (fun z hz => surgeryBall_image_subset_component B x hx ⟨z, hz, rfl⟩)
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    open_embedding := ?_ }
  · apply B.inverse_smooth.comp (E.map_smooth.mono (Set.subset_univ _))
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz, (hmap z hz).symm⟩
  · intro z hz
    change B.inverse (E.map (E.inverse (B.map z))) = z
    rw [hmap z hz]
    exact B.left_inverse hz
  · rintro y ⟨z, hz, rfl⟩
    change E.inverse (B.map (B.inverse (E.map (E.inverse (B.map z))))) = E.inverse (B.map z)
    rw [hmap z hz, B.left_inverse hz]
  · have hE : Topology.IsOpenEmbedding E.map :=
      (componentOpen A x).isOpen.isOpenEmbedding_subtypeVal
    apply Topology.IsOpenEmbedding.of_comp _ hE
    have hfun : E.map ∘
        (fun z : Metric.ball (0 : StandardCapSpace) 2 => (E.inverse ∘ B.map) z.val) =
          (fun z : Metric.ball (0 : StandardCapSpace) 2 => B.map z.val) := by
      funext z
      exact hmap z.val z.property
    rw [hfun]
    exact B.open_embedding

theorem componentBall_map_val (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x)
    {z : StandardCapSpace} (hz : z ∈ Metric.ball (0 : StandardCapSpace) 2) :
    ((componentBall B x hx).map z).val = B.map z :=
  (componentRegionEquivalence A x).right_inverse
    (surgeryBall_image_subset_component B x hx ⟨z, hz, rfl⟩)

theorem componentBall_inverse (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x)
    (z : (componentCarrier A x).carrier) :
    (componentBall B x hx).inverse z = B.inverse z.val := rfl

theorem componentBall_closedBall_image (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x) :
    Subtype.val '' (componentBall B x hx).closedBall = B.closedBall := by
  change Subtype.val '' ((componentBall B x hx).map '' Metric.closedBall (0 : StandardCapSpace) 1) =
    B.map '' Metric.closedBall (0 : StandardCapSpace) 1
  rw [← Set.image_comp]
  apply Set.image_congr
  intro z hz
  exact componentBall_map_val B x hx
    (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz)

end PoincareConjecture.M38
