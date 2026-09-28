import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem neck_carrier_isPreconnected
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : IsPreconnected N.carrier := by
  have heq : N.region (-N.epsilon⁻¹) N.epsilon⁻¹ = N.carrier := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (N.coordinate_inverse_mem x hx).2⟩⟩
  rw [← heq]
  exact N.region_isPreconnected le_rfl le_rfl


theorem neck_central_sphere_isConnected
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : IsConnected N.central_sphere := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let : PreconnectedSpace UnitTwoSphere :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_sphere hrank 0 1)
  refine ⟨⟨N.center, N.center_on_central_sphere⟩, ?_⟩
  rw [N.central_sphere_eq]
  apply (isPreconnected_univ.prod isPreconnected_singleton).image N.coordinate_map
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro ⟨z, s⟩ ⟨_, hs⟩
  have hs0 : s = 0 := hs
  subst s
  exact ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr N.epsilon_pos),
    inv_pos.mpr N.epsilon_pos⟩


def preAttachment (event : SurgeryEventData g0 K P slice metric T)
    (i : Fin event.cap_count) : Set (slice event.tMinus).carrier :=
  event.limit_identify.inverse '' (event.necks i).neck.central_sphere


theorem preAttachment_subset_retained
    (event : SurgeryEventData g0 K P slice metric T) (i : Fin event.cap_count) :
    preAttachment event i ⊆ event.retained_pre := by
  intro x hx
  apply event.retained_pre_compact.isClosed.frontier_subset
  rw [event.pre_boundary]
  exact mem_iUnion.mpr ⟨i, hx⟩


theorem preAttachment_isConnected
    (event : SurgeryEventData g0 K P slice metric T) (i : Fin event.cap_count) :
    IsConnected (preAttachment event i) :=
  (neck_central_sphere_isConnected (event.necks i).neck).image
    event.limit_identify.inverse (event.limit_identify.inverse_smooth.continuousOn.mono
      (subset_univ _))


def surgeryPostLabel (event : SurgeryEventData g0 K P slice metric T)
    (S : Set (slice event.tMinus).carrier) : Set (slice T).carrier :=
  event.retention.map '' (event.retained_pre ∩ S) ∪
    ⋃ i : {i : Fin event.cap_count // preAttachment event i ⊆ S}, (event.caps i.1).carrier


theorem surgeryPostLabel_isCompact
    (event : SurgeryEventData g0 K P slice metric T)
    {S : Set (slice event.tMinus).carrier} (hS : IsClosed S) :
    IsCompact (surgeryPostLabel event S) := by
  apply IsCompact.union
  · exact (event.retained_pre_compact.inter_right hS).image_of_continuousOn
      (event.retention.map_smooth.continuousOn.mono inter_subset_left)
  · exact isCompact_iUnion (fun i => (event.caps i.1).carrier_compact)

private theorem attachment_in_retained_label
    (event : SurgeryEventData g0 K P slice metric T)
    {S : Set (slice event.tMinus).carrier} {i : Fin event.cap_count}
    (hi : preAttachment event i ⊆ S)
    {x : (slice event.tMinus).carrier} (hx : x ∈ event.retained_pre)
    (hcap : event.retention.map x ∈ (event.caps i).carrier) : x ∈ S := by
  have hpost : event.retention.map x ∈ event.retained_post :=
    event.retention.map_image.subset (mem_image_of_mem event.retention.map hx)
  have hb : event.retention.map x ∈ frontier (event.caps i).carrier := by
    rw [← event.cap_boundary i]
    exact ⟨hpost, hcap⟩
  rw [← event.boundary_correspondence i] at hb
  obtain ⟨z, hz, heq⟩ := hb
  have heq' : z = x := event.retention.left_inverse.injOn
    (preAttachment_subset_retained event i hz) hx heq
  exact heq' ▸ hi hz


theorem surgeryPostLabel_disjoint
    (event : SurgeryEventData g0 K P slice metric T)
    (S : Set (slice event.tMinus).carrier) :
    Disjoint (surgeryPostLabel event S) (surgeryPostLabel event Sᶜ) := by
  apply Set.disjoint_left.mpr
  intro y hy hz
  rcases hy with ⟨x, hx, rfl⟩ | hy
  · rcases hz with ⟨z, hz, heq⟩ | hz
    · have hzx : z = x := event.retention.left_inverse.injOn hz.1 hx.1 heq
      exact hz.2 (hzx.symm ▸ hx.2)
    · obtain ⟨⟨i, hi⟩, hcap⟩ := mem_iUnion.mp hz
      exact attachment_in_retained_label event hi hx.1 hcap hx.2
  · obtain ⟨⟨i, hi⟩, hy⟩ := mem_iUnion.mp hy
    rcases hz with ⟨z, hz, rfl⟩ | hz
    · exact hz.2 (attachment_in_retained_label event hi hz.1 hy)
    · obtain ⟨⟨j, hj⟩, hz⟩ := mem_iUnion.mp hz
      by_cases hij : i = j
      · subst j
        obtain ⟨x, hx⟩ := (preAttachment_isConnected event i).nonempty
        exact hj hx (hi hx)
      · exact Set.disjoint_left.mp (event.cap_disjoint i j hij) hy hz


theorem surgeryPostLabel_union_compl
    (event : SurgeryEventData g0 K P slice metric T)
    {S : Set (slice event.tMinus).carrier} (hS : IsClopen S) :
    surgeryPostLabel event S ∪ surgeryPostLabel event Sᶜ = univ := by
  apply eq_univ_of_forall
  intro y
  have hy : y ∈ event.retained_post ∪ ⋃ i, (event.caps i).carrier :=
    event.post_cover.symm ▸ mem_univ y
  rcases hy with hy | hy
  · rw [← event.retention.map_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases hxS : x ∈ S
    · exact Or.inl (Or.inl ⟨x, ⟨hx, hxS⟩, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, ⟨hx, hxS⟩, rfl⟩)
  · obtain ⟨i, hy⟩ := mem_iUnion.mp hy
    rcases disjoint_or_subset_of_isClopen
        (preAttachment_isConnected event i).isPreconnected hS with hi | hi
    · have hi' : preAttachment event i ⊆ Sᶜ := fun x hx hxs =>
        Set.disjoint_left.mp hi hx hxs
      exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨i, hi'⟩, hy⟩))
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hy⟩))


theorem surgeryPostLabel_isClopen
    (event : SurgeryEventData g0 K P slice metric T)
    {S : Set (slice event.tMinus).carrier} (hS : IsClopen S) :
    IsClopen (surgeryPostLabel event S) := by
  have hclosed := (surgeryPostLabel_isCompact event hS.isClosed).isClosed
  have hother := (surgeryPostLabel_isCompact event hS.compl.isClosed).isClosed
  have heq : (surgeryPostLabel event S)ᶜ = surgeryPostLabel event Sᶜ := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ surgeryPostLabel event S ∪ surgeryPostLabel event Sᶜ :=
        (surgeryPostLabel_union_compl event hS).symm ▸ mem_univ x
      exact hu.resolve_left hx
    · intro hx hxs
      exact Set.disjoint_left.mp (surgeryPostLabel_disjoint event S) hxs hx
  refine ⟨hclosed, ?_⟩
  have hopen := hother.isOpen_compl
  rwa [← heq, compl_compl] at hopen


theorem inverse_neck_subset_of_attachment_label
    (event : SurgeryEventData g0 K P slice metric T)
    {S : Set (slice event.tMinus).carrier} (hS : IsClopen S)
    (i : Fin event.cap_count) (hi : preAttachment event i ⊆ S) :
    event.limit_identify.inverse '' (event.necks i).neck.carrier ⊆ S := by
  have hconn := (neck_carrier_isPreconnected (event.necks i).neck).image
    event.limit_identify.inverse (event.limit_identify.inverse_smooth.continuousOn.mono
      (subset_univ _))
  apply hconn.subset_isClopen hS
  obtain ⟨x, hx⟩ := (preAttachment_isConnected event i).nonempty
  exact ⟨x, image_mono (event.necks i).neck.central_sphere_subset hx, hi hx⟩

end PoincareConjecture.Proofs.M46
