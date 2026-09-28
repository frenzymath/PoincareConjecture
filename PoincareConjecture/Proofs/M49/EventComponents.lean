import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M49.NeckCoordinates
import PoincareConjecture.Proofs.M49.Mathlib.FiniteComponents
import Mathlib.Analysis.Normed.Module.Connected











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M49

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem epsilonNeck_isConnected_central_sphere (N : EpsilonNeck g) :
    IsConnected N.central_sphere := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace UnitTwoSphere :=
    Subtype.connectedSpace (isConnected_sphere hdim (0 : EuclideanSpace ℝ (Fin 3))
      (by norm_num : (0 : ℝ) ≤ 1))
  rw [N.central_sphere_eq]
  refine ((isConnected_univ : IsConnected (univ : Set UnitTwoSphere)).prod
    isConnected_singleton).image N.coordinate_map ?_
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have ht0 : t = 0 := mem_singleton_iff.mp ht
  subst t
  exact ⟨hq, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩



theorem epsilonNeck_negative_half_nonempty (N : EpsilonNeck g) :
    (N.region (-N.epsilon⁻¹) 0).Nonempty := by
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  rw [← epsilonNeckChart_image_region N (-N.epsilon⁻¹) 0 le_rfl he.le]
  apply Set.Nonempty.image
  refine ⟨((N.coordinate_inverse N.center).1, -N.epsilon⁻¹ / 2), mem_univ _, ?_⟩
  constructor <;> linarith

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem event_boundary_isConnected
    (E : SurgeryEventData g0 K P slice metric T) (i : Fin E.cap_count) :
    IsConnected (E.limit_identify.inverse '' (E.necks i).neck.central_sphere) := by
  exact (epsilonNeck_isConnected_central_sphere (E.necks i).neck).image
    E.limit_identify.inverse (E.limit_identify.inverse_smooth.continuousOn.mono
      (subset_univ _))




theorem event_post_component_meets_retained
    (E : SurgeryEventData g0 K P slice metric T) (y : (slice T).carrier) :
    ∃ z ∈ E.retained_post, z ∈ connectedComponent y := by
  have hy : y ∈ E.retained_post ∪ ⋃ i, (E.caps i).carrier := by
    rw [E.post_cover]
    exact mem_univ _
  rcases hy with hy | hy
  · exact ⟨y, hy, mem_connectedComponent⟩
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
  obtain ⟨e⟩ := (E.local_result i).open_ball_model
  let : ConnectedSpace (E.local_result i).output.carrier :=
    (e.trans Homeomorph.ulift).connectedSpace_iff.mpr inferInstance
  have hc : IsConnected (range (E.local_embed i)) :=
    isConnected_range (E.local_embed_smooth i).continuous
  have hyc : y ∈ range (E.local_embed i) := by
    rw [← E.local_cap_image i] at hyi
    obtain ⟨w, _, rfl⟩ := hyi
    exact mem_range_self _
  obtain ⟨a, ha⟩ := epsilonNeck_negative_half_nonempty (E.necks i).neck
  obtain ⟨x, hx, hxa⟩ := E.neck_negative_retained i ha
  have hinv : E.limit_identify.inverse a ∈ E.retained_pre := by
    rw [← hxa, E.limit_identify.left_inverse (E.retained_pre_subset hx)]
    exact hx
  refine ⟨E.local_embed i ((E.local_result i).collapse a), ?_,
    hc.subset_connectedComponent hyc (mem_range_self _)⟩
  rw [E.local_retention i a ha]
  exact E.retention.map_image.subset (mem_image_of_mem _ hinv)




theorem event_retention_connectedComponentsMap_surjective
    (E : SurgeryEventData g0 K P slice metric T) :
    Function.Surjective
      E.retention.map_smooth.continuousOn.domRestrict.connectedComponentsMap := by
  intro c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨z, hz, hzy⟩ := event_post_component_meets_retained E y
  rw [← E.retention.map_image] at hz
  obtain ⟨x, hx, hxz⟩ := hz
  refine ⟨ConnectedComponents.mk ⟨x, hx⟩, ?_⟩
  change ConnectedComponents.mk (E.retention.map x) = ConnectedComponents.mk y
  rw [hxz]
  exact ConnectedComponents.coe_eq_coe'.mpr hzy




theorem event_retained_components_finite
    (E : SurgeryEventData g0 K P slice metric T)
    [Finite (ConnectedComponents (slice E.tMinus).carrier)] :
    Finite (ConnectedComponents E.retained_pre) := by
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice E.tMinus).carrier
  apply E.retained_pre_compact.isClosed.finite_connectedComponents_of_frontier_cover
    (fun i => E.limit_identify.inverse '' (E.necks i).neck.central_sphere)
    (fun i => (event_boundary_isConnected E i).isPreconnected)
  · intro i x hx
    apply E.retained_pre_compact.isClosed.frontier_subset
    rw [E.pre_boundary]
    exact mem_iUnion.mpr ⟨i, hx⟩
  · exact E.pre_boundary.subset



theorem event_post_components_finite
    (E : SurgeryEventData g0 K P slice metric T)
    [Finite (ConnectedComponents (slice E.tMinus).carrier)] :
    Finite (ConnectedComponents (slice T).carrier) := by
  let := event_retained_components_finite E
  exact Finite.of_surjective
    E.retention.map_smooth.continuousOn.domRestrict.connectedComponentsMap
    (event_retention_connectedComponentsMap_surjective E)



theorem event_components_card_le
    (E : SurgeryEventData g0 K P slice metric T)
    [Finite (ConnectedComponents (slice E.tMinus).carrier)] :
    Nat.card (ConnectedComponents (slice T).carrier) ≤
      Nat.card (ConnectedComponents (slice E.tMinus).carrier) + E.cap_count := by
  let := event_retained_components_finite E
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice E.tMinus).carrier
  have hpost := Nat.card_le_card_of_surjective
    E.retention.map_smooth.continuousOn.domRestrict.connectedComponentsMap
    (event_retention_connectedComponentsMap_surjective E)
  have hret := E.retained_pre_compact.isClosed.card_connectedComponents_le_of_frontier_cover
    (fun i => E.limit_identify.inverse '' (E.necks i).neck.central_sphere)
    (fun i => (event_boundary_isConnected E i).isPreconnected)
    (fun i x hx => E.retained_pre_compact.isClosed.frontier_subset
      (E.pre_boundary.symm ▸ mem_iUnion.mpr ⟨i, hx⟩)) E.pre_boundary.subset
  exact hpost.trans (by simpa using hret)




theorem event_components_card_add_one_le
    (E : SurgeryEventData g0 K P slice metric T)
    [Finite (ConnectedComponents (slice E.tMinus).carrier)]
    (hzero : E.cap_count = 0) (x : (slice E.tMinus).carrier)
    (hx : connectedComponent x ⊆ E.retained_preᶜ) :
    Nat.card (ConnectedComponents (slice T).carrier) + 1 ≤
      Nat.card (ConnectedComponents (slice E.tMinus).carrier) := by
  let := event_retained_components_finite E
  have hpost := Nat.card_le_card_of_surjective
    E.retention.map_smooth.continuousOn.domRestrict.connectedComponentsMap
    (event_retention_connectedComponentsMap_surjective E)
  have hclopen : IsClopen E.retained_pre := by
    apply isClopen_iff_frontier_eq_empty.mpr
    apply subset_empty_iff.mp
    intro y hy
    rw [E.pre_boundary] at hy
    obtain ⟨i, _⟩ := mem_iUnion.mp hy
    have hi := i.isLt
    omega
  exact Nat.add_one_le_iff.mpr
    (hpost.trans_lt (hclopen.card_connectedComponents_lt_of_component_omitted x hx))

end PoincareConjecture.M49
