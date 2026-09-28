import PoincareConjecture.Proofs.M36.NeckCoordinates
import PoincareConjecture.Proofs.M49.EventComponents









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem m56Event_negative_interior
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    {z : E.terminal.carrier}
    (hz : z ∈ (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0) :
    E.limit_identify.inverse z ∈ interior E.retained_pre := by
  let U := E.regular_limit ∩ E.limit_identify.map ⁻¹'
    (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0
  have hopen : IsOpen U := E.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
    E.regular_limit_open (M36.neck_region_isOpen _ _ _)
  have hsub : U ⊆ E.retained_pre := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := E.neck_negative_retained i hx.2
    have hxy : x = y := by
      have h := congrArg E.limit_identify.inverse heq
      rw [E.limit_identify.left_inverse (E.retained_pre_subset hy),
        E.limit_identify.left_inverse hx.1] at h
      exact h.symm
    exact hxy.symm ▸ hy
  apply interior_maximal hsub hopen
  refine ⟨E.limit_identify.inverse_image.subset ⟨z, mem_univ _, rfl⟩, ?_⟩
  change E.limit_identify.map (E.limit_identify.inverse z) ∈
    (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0
  rwa [E.limit_identify.right_inverse (mem_univ z)]



theorem m56Event_cap_meets_retainedInterior
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count)
    {y : (slice T).carrier} (hy : y ∈ (E.caps i).carrier) :
    ∃ x ∈ interior E.retained_pre,
      E.retention.map x ∈ connectedComponent y := by
  obtain ⟨e⟩ := (E.local_result i).open_ball_model
  let : ConnectedSpace (E.local_result i).output.carrier :=
    (e.trans Homeomorph.ulift).connectedSpace_iff.mpr inferInstance
  have hc : IsConnected (range (E.local_embed i)) :=
    isConnected_range (E.local_embed_smooth i).continuous
  have hyc : y ∈ range (E.local_embed i) := by
    rw [← E.local_cap_image i] at hy
    obtain ⟨w, _, rfl⟩ := hy
    exact mem_range_self _
  obtain ⟨z, hz⟩ := M49.epsilonNeck_negative_half_nonempty (E.necks i).neck
  refine ⟨E.limit_identify.inverse z, m56Event_negative_interior E i hz, ?_⟩
  rw [← E.local_retention i z hz]
  exact hc.subset_connectedComponent hyc (mem_range_self _)



theorem m56Event_component_meets_retainedInterior
    (E : SurgeryEventData g0 K P slice metric T) (y : (slice T).carrier) :
    ∃ x ∈ interior E.retained_pre,
      E.retention.map x ∈ connectedComponent y := by
  obtain ⟨z, hz, hzy⟩ := M49.event_post_component_meets_retained E y
  rw [← E.retention.map_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  by_cases hint : x ∈ interior E.retained_pre
  · exact ⟨x, hint, hzy⟩
  have hfront : x ∈ frontier E.retained_pre := by
    rw [frontier, E.retained_pre_compact.isClosed.closure_eq]
    exact ⟨hx, hint⟩
  rw [E.pre_boundary] at hfront
  obtain ⟨i, hi⟩ := mem_iUnion.mp hfront
  have hcapfront : E.retention.map x ∈ frontier (E.caps i).carrier := by
    rw [← E.boundary_correspondence i]
    exact mem_image_of_mem _ hi
  have hcap := (E.caps i).carrier_compact.isClosed.frontier_subset hcapfront
  obtain ⟨w, hw, hcomp⟩ := m56Event_cap_meets_retainedInterior E i hcap
  exact ⟨w, hw, (connectedComponent_eq hzy) ▸ hcomp⟩

end PoincareConjecture
