import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventCapCoordinates

/-!
# Retention identifies the exact open complement of the inserted caps

The stored boundary correspondence and cover identify the interior of the
retained pre-region with the complement of all actual inserted closed cap
balls. The maps are the original event retention maps.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

/-- The image of the entire pre-boundary is precisely the union of all
actual post-cap boundaries. -/
theorem retention_frontier_image :
    (F.event T hT).retention.map '' frontier (F.event T hT).retained_pre =
      ⋃ i, frontier ((F.event T hT).caps i).carrier := by
  rw [(F.event T hT).pre_boundary, Set.image_iUnion]
  congr 1
  funext i
  exact (F.event T hT).boundary_correspondence i

/-- The retained post-region meets the inserted caps exactly in their
union of boundaries. -/
theorem retained_post_inter_caps :
    (F.event T hT).retained_post ∩ (⋃ i, ((F.event T hT).caps i).carrier) =
      ⋃ i, frontier ((F.event T hT).caps i).carrier := by
  rw [Set.inter_iUnion]
  congr 1
  funext i
  exact (F.event T hT).cap_boundary i

/-- Removing these boundaries from the retained post-region is the same
as taking the complement of the actual closed caps in the whole slice. -/
theorem retained_post_sdiff_boundaries :
    (F.event T hT).retained_post \ (⋃ i, frontier ((F.event T hT).caps i).carrier) =
      (⋃ i, ((F.event T hT).caps i).carrier)ᶜ := by
  rw [← retained_post_inter_caps]
  ext y
  constructor
  · rintro ⟨hy, hnot⟩ hcap
    exact hnot ⟨hy, hcap⟩
  · intro hnot
    have hy : y ∈ (F.event T hT).retained_post ∪ (⋃ i, ((F.event T hT).caps i).carrier) := by
      rw [(F.event T hT).post_cover]
      exact Set.mem_univ _
    exact ⟨hy.resolve_right hnot, fun h => hnot h.2⟩

/-- The actual retention maps the old interior onto the exact cap
complement, with no change of the selected event data. -/
theorem retention_interior_image :
    (F.event T hT).retention.map '' interior (F.event T hT).retained_pre =
      (⋃ i, ((F.event T hT).caps i).carrier)ᶜ := by
  rw [← self_sdiff_frontier (F.event T hT).retained_pre,
    (F.event T hT).retention.left_inverse.injOn.image_sdiff_subset
      (F.event T hT).retained_pre_compact.isClosed.frontier_subset,
    (F.event T hT).retention.map_image, retention_frontier_image,
    retained_post_sdiff_boundaries]

/-- The unchanged retention inverse maps this exact cap complement back
onto the old retained interior. -/
theorem retention_inverse_cap_complement_image :
    (F.event T hT).retention.inverse '' (⋃ i, ((F.event T hT).caps i).carrier)ᶜ =
      interior (F.event T hT).retained_pre := by
  rw [← retention_interior_image]
  exact (F.event T hT).retention.left_inverse.image_image' interior_subset

/-- The full-slice retention maps restrict smoothly to the two exact
interiors needed by the connected-sum reconstruction. -/
noncomputable def retentionInteriorEquivalence :
    SurgeryRegionEquivalence (F.slice (F.event T hT).tMinus) (F.slice T)
      (interior (F.event T hT).retained_pre)
      ((⋃ i, ((F.event T hT).caps i).carrier)ᶜ) where
  map := (F.event T hT).retention.map
  inverse := (F.event T hT).retention.inverse
  map_image := retention_interior_image F T hT
  inverse_image := retention_inverse_cap_complement_image F T hT
  left_inverse := (F.event T hT).retention.left_inverse.mono interior_subset
  right_inverse := by
    intro y hy
    apply (F.event T hT).retention.right_inverse
    rw [← retained_post_sdiff_boundaries] at hy
    exact hy.1
  map_smooth := (F.event T hT).retention.map_smooth.mono interior_subset
  inverse_smooth := (F.event T hT).retention.inverse_smooth.mono (by
    intro y hy
    rw [← retained_post_sdiff_boundaries] at hy
    exact hy.1)

/-- The inverse direction uses the same two total event maps. -/
noncomputable def retentionInteriorInverseEquivalence :
    SurgeryRegionEquivalence (F.slice T) (F.slice (F.event T hT).tMinus)
      ((⋃ i, ((F.event T hT).caps i).carrier)ᶜ)
      (interior (F.event T hT).retained_pre) where
  map := (retentionInteriorEquivalence F T hT).inverse
  inverse := (retentionInteriorEquivalence F T hT).map
  map_image := (retentionInteriorEquivalence F T hT).inverse_image
  inverse_image := (retentionInteriorEquivalence F T hT).map_image
  left_inverse := (retentionInteriorEquivalence F T hT).right_inverse
  right_inverse := (retentionInteriorEquivalence F T hT).left_inverse
  map_smooth := (retentionInteriorEquivalence F T hT).inverse_smooth
  inverse_smooth := (retentionInteriorEquivalence F T hT).map_smooth

end PoincareMT.M38
