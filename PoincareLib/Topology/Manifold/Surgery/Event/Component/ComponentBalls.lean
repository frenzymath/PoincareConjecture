import PoincareLib.Topology.Manifold.Surgery.Event.Retained.RetainedComponents

/-!
# The actual ball embedding in its incident component

Restrict a supplied ball to an actual open component using the existing
component equivalence. Inclusion keeps every radius-two coordinate and
the entire closed unit ball unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

/-- The entire extended chart image of an actual ball is connected. -/
theorem surgeryBall_image_connected :
    IsConnected (B.map '' Metric.ball (0 : StandardCapSpace) 2) := by
  let : ConnectedSpace (Metric.ball (0 : StandardCapSpace) 2) := capDoubleBall_connected
  have h := isConnected_range B.open_embedding.continuous
  change IsConnected (Set.range (B.map ∘
    (Subtype.val : Metric.ball (0 : StandardCapSpace) 2 → StandardCapSpace))) at h
  simpa only [Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h

/-- The full ball chart belongs to the component of its literal center. -/
theorem surgeryBall_image_subset_center_component :
    B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ connectedComponent (B.map 0) :=
  (surgeryBall_image_connected B).subset_connectedComponent ⟨0, by simp, rfl⟩

/-- Any representative in that same component also contains the entire chart. -/
theorem surgeryBall_image_subset_component (x : A.carrier)
    (hx : B.map 0 ∈ connectedComponent x) :
    B.map '' Metric.ball (0 : StandardCapSpace) 2 ⊆ connectedComponent x := by
  simpa only [connectedComponent_eq hx] using surgeryBall_image_subset_center_component B

/-- Restrict the exact supplied ball to its actual incident component.
The region inverse's fallback is used only away from the ball's domain. -/
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

/-- Inclusion preserves the actual map on its full radius-two domain. -/
theorem componentBall_map_val (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x)
    {z : StandardCapSpace} (hz : z ∈ Metric.ball (0 : StandardCapSpace) 2) :
    ((componentBall B x hx).map z).val = B.map z :=
  (componentRegionEquivalence A x).right_inverse
    (surgeryBall_image_subset_component B x hx ⟨z, hz, rfl⟩)

/-- The restricted inverse is the original ball inverse after literal inclusion. -/
theorem componentBall_inverse (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x)
    (z : (componentCarrier A x).carrier) :
    (componentBall B x hx).inverse z = B.inverse z.val := rfl

/-- The entire restricted closed unit ball has exactly its original ambient image. -/
theorem componentBall_closedBall_image (x : A.carrier) (hx : B.map 0 ∈ connectedComponent x) :
    Subtype.val '' (componentBall B x hx).closedBall = B.closedBall := by
  change Subtype.val '' ((componentBall B x hx).map '' Metric.closedBall (0 : StandardCapSpace) 1) =
    B.map '' Metric.closedBall (0 : StandardCapSpace) 1
  rw [← Set.image_comp]
  apply Set.image_congr
  intro z hz
  exact componentBall_map_val B x hx
    (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz)

end PoincareMT.M38
