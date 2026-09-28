import PoincareConjecture.Proofs.M38.EventCapCoordinates









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]



theorem retention_frontier_image :
    (F.event T hT).retention.map '' frontier (F.event T hT).retained_pre =
      ⋃ i, frontier ((F.event T hT).caps i).carrier := by
  rw [(F.event T hT).pre_boundary, Set.image_iUnion]
  congr 1
  funext i
  exact (F.event T hT).boundary_correspondence i



theorem retained_post_inter_caps :
    (F.event T hT).retained_post ∩ (⋃ i, ((F.event T hT).caps i).carrier) =
      ⋃ i, frontier ((F.event T hT).caps i).carrier := by
  rw [Set.inter_iUnion]
  congr 1
  funext i
  exact (F.event T hT).cap_boundary i



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



theorem retention_interior_image :
    (F.event T hT).retention.map '' interior (F.event T hT).retained_pre =
      (⋃ i, ((F.event T hT).caps i).carrier)ᶜ := by
  rw [← self_sdiff_frontier (F.event T hT).retained_pre,
    (F.event T hT).retention.left_inverse.injOn.image_sdiff_subset
      (F.event T hT).retained_pre_compact.isClosed.frontier_subset,
    (F.event T hT).retention.map_image, retention_frontier_image,
    retained_post_sdiff_boundaries]



theorem retention_inverse_cap_complement_image :
    (F.event T hT).retention.inverse '' (⋃ i, ((F.event T hT).caps i).carrier)ᶜ =
      interior (F.event T hT).retained_pre := by
  rw [← retention_interior_image]
  exact (F.event T hT).retention.left_inverse.image_image' interior_subset



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

end PoincareConjecture.M38
