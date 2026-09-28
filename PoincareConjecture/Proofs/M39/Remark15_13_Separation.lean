import PoincareConjecture.Proofs.M39.Prop15_12_MapConstruction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

section RetainedRoot

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T)

theorem cap_subset_child_of_inter_nonempty (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hi : ((E.caps i).carrier ∩ range C.inclusion).Nonempty) :
    (E.caps i).carrier ⊆ range C.inclusion := by
  apply cap_subset_child E i C
  apply local_embed_range_subset_child E i C
  obtain ⟨y, hy, hC⟩ := hi
  rw [← E.local_cap_image i] at hy
  obtain ⟨z, _, rfl⟩ := hy
  exact ⟨z, hC⟩

theorem retained_cap_attachment_isPreconnected (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T)) :
    IsPreconnected ((E.retained_post ∩ range C.inclusion) ∩
      ((E.caps i).carrier ∩ range C.inclusion)) := by
  by_cases hi : ((E.caps i).carrier ∩ range C.inclusion).Nonempty
  · have hsub := cap_subset_child_of_inter_nonempty E i C hi
    have heq : (E.retained_post ∩ range C.inclusion) ∩
        ((E.caps i).carrier ∩ range C.inclusion) = frontier (E.caps i).carrier := by
      rw [← E.cap_boundary i]
      ext x
      exact ⟨fun hx => ⟨hx.1.1, hx.2.1⟩,
        fun hx => ⟨⟨hx.1, hsub hx.2⟩, ⟨hx.2, hsub hx.2⟩⟩⟩
    rw [heq]
    exact (cap_frontier_isConnected E i).isPreconnected
  · rw [Set.not_nonempty_iff_eq_empty.mp hi, inter_empty]
    exact isPreconnected_empty

theorem retainedPost_in_child_isPreconnected
    (C : SurgerySelectedComponent (slice T)) :
    IsPreconnected (E.retained_post ∩ range C.inclusion) := by
  classical
  let S := range C.inclusion
  let A := E.retained_post ∩ S
  let B : Fin E.cap_count → Set (slice T).carrier := fun i => (E.caps i).carrier ∩ S
  have hS : IsClosed S := by
    rw [show S = connectedComponent (C.inclusion C.basepoint) from C.range_eq_component]
    exact isClosed_connectedComponent
  have hSconn : IsPreconnected S := by
    rw [show S = connectedComponent (C.inclusion C.basepoint) from C.range_eq_component]
    exact isPreconnected_connectedComponent
  have hA : IsClosed A := E.retained_post_compact.isClosed.inter hS
  have hB (i : Fin E.cap_count) : IsClosed (B i) :=
    (E.caps i).carrier_compact.isClosed.inter hS
  have hattach (i : Fin E.cap_count) : IsPreconnected (A ∩ B i) :=
    retained_cap_attachment_isPreconnected E i C
  have hcover : S ⊆ A ∪ ⋃ i, B i := by
    intro x hx
    have hpost : x ∈ E.retained_post ∪ ⋃ i, (E.caps i).carrier := by
      rw [E.post_cover]
      exact mem_univ x
    rcases hpost with ha | hb
    · exact Or.inl ⟨ha, hx⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      exact Or.inr (mem_iUnion.mpr ⟨i, hi, hx⟩)
  change IsPreconnected A
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hA).mpr
  intro u v hu hv huv hdisj
  let J : Set (Fin E.cap_count) := {i | A ∩ B i ⊆ u}
  have hright (i : Fin E.cap_count) (hi : i ∉ J) : A ∩ B i ⊆ v := by
    exact ((isPreconnected_iff_subset_of_fully_disjoint_closed (hA.inter (hB i))).mp
      (hattach i) u v hu hv (inter_subset_left.trans huv) hdisj).resolve_left hi
  let L := (A ∩ u) ∪ ⋃ i ∈ J, B i
  let R := (A ∩ v) ∪ ⋃ i ∈ Jᶜ, B i
  have hL : IsClosed L :=
    (hA.inter hu).union ((Set.toFinite J).isClosed_biUnion (fun i _ => hB i))
  have hR : IsClosed R :=
    (hA.inter hv).union ((Set.toFinite Jᶜ).isClosed_biUnion (fun i _ => hB i))
  have hLA : A ∩ L ⊆ u := by
    rintro x ⟨hxA, hx⟩
    rcases hx with hx | hx
    · exact hx.2
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := mem_iUnion.mp hi
      exact hi ⟨hxA, hxi⟩
  have hRA : A ∩ R ⊆ v := by
    rintro x ⟨hxA, hx⟩
    rcases hx with hx | hx
    · exact hx.2
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := mem_iUnion.mp hi
      exact hright i hi ⟨hxA, hxi⟩
  have hLR : Disjoint L R := by
    apply Set.disjoint_left.mpr
    intro x hxL hxR
    rcases hxL with hxu | hxi
    · exact Set.disjoint_left.mp hdisj hxu.2 (hRA ⟨hxu.1, hxR⟩)
    rcases hxR with hxv | hxj
    · exact Set.disjoint_left.mp hdisj (hLA ⟨hxv.1, Or.inr hxi⟩) hxv.2
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxi
    obtain ⟨hi, hxi⟩ := mem_iUnion.mp hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxj
    obtain ⟨hj, hxj⟩ := mem_iUnion.mp hj
    by_cases hij : i = j
    · subst j
      exact hj hi
    · exact Set.disjoint_left.mp (E.cap_disjoint i j hij) hxi.1 hxj.1
  have hLRcover : S ⊆ L ∪ R := by
    intro x hx
    rcases hcover hx with ha | hb
    · rcases huv ha with hu | hv
      · exact Or.inl (Or.inl ⟨ha, hu⟩)
      · exact Or.inr (Or.inl ⟨ha, hv⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      by_cases hj : i ∈ J
      · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hj, hi⟩⟩))
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hj, hi⟩⟩))
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hS).mp hSconn
    L R hL hR hLRcover hLR with hleft | hright
  · exact Or.inl (fun x hx => hLA ⟨hx, hleft hx.2⟩)
  · exact Or.inr (fun x hx => hRA ⟨hx, hright hx.2⟩)

theorem retainedPost_in_child_isConnected
    (C : SurgerySelectedComponent (slice T)) :
    IsConnected (E.retained_post ∩ range C.inclusion) := by
  refine ⟨?_, retainedPost_in_child_isPreconnected E C⟩
  have hbase : C.inclusion C.basepoint ∈ E.retained_post ∪ ⋃ i, (E.caps i).carrier := by
    rw [E.post_cover]
    exact mem_univ _
  rcases hbase with hbase | hbase
  · exact ⟨C.inclusion C.basepoint, hbase, mem_range_self _⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hbase
    have hsub := cap_subset_child_of_inter_nonempty E i C
      ⟨C.inclusion C.basepoint, hi, mem_range_self _⟩
    obtain ⟨x, hx⟩ := (cap_frontier_isConnected E i).nonempty
    rw [← E.cap_boundary i] at hx
    exact ⟨x, hx.1, hsub hx.2⟩

def retainedPreRoot (C : SurgerySelectedComponent (slice T)) :
    Set (slice E.tMinus).carrier :=
  E.retention.inverse '' (E.retained_post ∩ range C.inclusion)

theorem mem_retainedPreRoot_iff (C : SurgerySelectedComponent (slice T))
    (x : (slice E.tMinus).carrier) :
    x ∈ retainedPreRoot E C ↔
      x ∈ E.retained_pre ∧ E.retention.map x ∈ range C.inclusion := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · exact retention_inverse_mem_pre E hy.1
    · simpa only [E.retention.right_inverse hy.1] using hy.2
  · rintro ⟨hx, hC⟩
    refine ⟨E.retention.map x, ⟨?_, hC⟩, E.retention.left_inverse hx⟩
    exact retention_map_mem_post E hx

theorem retainedPreRoot_isConnected (C : SurgerySelectedComponent (slice T)) :
    IsConnected (retainedPreRoot E C) := by
  exact (retainedPost_in_child_isConnected E C).image E.retention.inverse
    (E.retention.inverse_smooth.continuousOn.mono inter_subset_left)

theorem retainedPreRoot_isCompact (C : SurgerySelectedComponent (slice T)) :
    IsCompact (retainedPreRoot E C) := by
  have hclosed : IsClosed (range C.inclusion) := by
    rw [C.range_eq_component]
    exact isClosed_connectedComponent
  exact (E.retained_post_compact.inter_right hclosed).image_of_continuousOn
    (E.retention.inverse_smooth.continuousOn.mono inter_subset_left)

end RetainedRoot

section ParentRoot

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

theorem retainedPreRoot_subset_parent :
    retainedPreRoot (D.flow.event T hT) I.child ⊆ range I.parent.inclusion := by
  obtain ⟨x, hx⟩ := I.inherited
  have hxroot : I.parent.inclusion x ∈ retainedPreRoot (D.flow.event T hT) I.child :=
    (mem_retainedPreRoot_iff _ _ _).mpr
      ⟨interior_subset (I.retained_subset x hx), I.retained_to_child x hx⟩
  have hsub := (retainedPreRoot_isConnected (D.flow.event T hT) I.child).subset_connectedComponent
    hxroot
  have hparent : I.parent.inclusion x ∈ connectedComponent
      (I.parent.inclusion I.parent.basepoint) := by
    rw [← I.parent.range_eq_component]
    exact mem_range_self x
  rw [I.parent.range_eq_component, connectedComponent_eq hparent]
  exact hsub

def retainedRoot : Set I.parent.carrier.carrier :=
  I.parent.inclusion ⁻¹' retainedPreRoot (D.flow.event T hT) I.child

theorem retainedRoot_isConnected : IsConnected (retainedRoot I) := by
  exact (retainedPreRoot_isConnected (D.flow.event T hT) I.child).preimage_of_isOpenMap
    I.parent.inclusion_openEmbedding.injective
      I.parent.inclusion_openEmbedding.isOpenMap (retainedPreRoot_subset_parent I)

theorem retainedRoot_isClosed : IsClosed (retainedRoot I) :=
  (retainedPreRoot_isCompact (D.flow.event T hT) I.child).isClosed.preimage
    I.parent.inclusion_openEmbedding.continuous

theorem retainedRoot_isCompact : IsCompact (retainedRoot I) :=
  I.parent.compact.of_isClosed_subset (retainedRoot_isClosed I) (subset_univ _)

theorem retained_eq_interior_root : I.retained = interior (retainedRoot I) := by
  have hsub : I.retained ⊆ retainedRoot I := by
    intro x hx
    exact (mem_retainedPreRoot_iff _ _ _).mpr
      ⟨interior_subset (I.retained_subset x hx), I.retained_to_child x hx⟩
  apply subset_antisymm (interior_maximal hsub I.retained_open)
  intro x hx
  have hxroot := (mem_retainedPreRoot_iff (D.flow.event T hT) I.child
    (I.parent.inclusion x)).mp (show x ∈ retainedRoot I from interior_subset hx)
  have himage : I.parent.inclusion '' interior (retainedRoot I) ⊆
      (D.flow.event T hT).retained_pre := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((mem_retainedPreRoot_iff (D.flow.event T hT) I.child
      (I.parent.inclusion y)).mp (show y ∈ retainedRoot I from interior_subset hy)).1
  have hopen := I.parent.inclusion_openEmbedding.isOpenMap _
    (isOpen_interior (s := retainedRoot I))
  rw [I.retained_eq]
  exact ⟨interior_maximal himage hopen ⟨x, hx, rfl⟩, hxroot.2⟩

def parentSphere (i : Fin (D.flow.event T hT).cap_count) :
    Set I.parent.carrier.carrier :=
  I.parent.inclusion ⁻¹' ((D.flow.event T hT).limit_identify.inverse ''
    ((D.flow.event T hT).necks i).neck.central_sphere)

def rootCaps : Set (Fin (D.flow.event T hT).cap_count) :=
  {i | (((D.flow.event T hT).caps i).carrier ∩ range I.child.inclusion).Nonempty}

theorem rootCap_local_output_in_child (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) :
    range ((D.flow.event T hT).local_embed i) ⊆ range I.child.inclusion := by
  apply local_embed_range_subset_child (D.flow.event T hT) i I.child
  obtain ⟨y, hy, hchild⟩ := hi
  rw [← (D.flow.event T hT).local_cap_image i] at hy
  obtain ⟨z, _, rfl⟩ := hy
  exact ⟨z, hchild⟩

theorem rootCap_negative_subset_root (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) :
    (D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.region
        (-((D.flow.event T hT).necks i).neck.epsilon⁻¹) 0 ⊆
      retainedPreRoot (D.flow.event T hT) I.child := by
  rintro x ⟨z, hz, rfl⟩
  apply (mem_retainedPreRoot_iff _ _ _).mpr
  constructor
  · obtain ⟨y, hy, hyz⟩ := (D.flow.event T hT).neck_negative_retained i hz
    rw [← hyz, (D.flow.event T hT).limit_identify.left_inverse
      ((D.flow.event T hT).retained_pre_subset hy)]
    exact hy
  · rw [← (D.flow.event T hT).local_retention i z hz]
    exact rootCap_local_output_in_child I i hi (mem_range_self _)

theorem positive_neck_disjoint_root (i : Fin (D.flow.event T hT).cap_count) :
    Disjoint ((D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.region 0
        ((D.flow.event T hT).necks i).neck.epsilon⁻¹)
      (retainedPreRoot (D.flow.event T hT) I.child) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z, hz, rfl⟩ hx
  have hpre := ((mem_retainedPreRoot_iff _ _ _).mp hx).1
  apply Set.disjoint_left.mp ((D.flow.event T hT).neck_positive_discarded i) hz
  exact ⟨_, hpre, (D.flow.event T hT).limit_identify.right_inverse (mem_univ z)⟩

theorem rootCap_preSphere_subset (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) :
    (D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.central_sphere ⊆
        retainedPreRoot (D.flow.event T hT) I.child := by
  intro x hx
  have hpre := preSphere_subset_retained (D.flow.event T hT) i hx
  apply (mem_retainedPreRoot_iff _ _ _).mpr
  exact ⟨hpre, cap_subset_child_of_inter_nonempty (D.flow.event T hT) i I.child hi
    ((retention_mem_cap_iff (D.flow.event T hT) i hpre).mpr hx)⟩

theorem rootCap_parentSphere_nonempty (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) : (parentSphere I i).Nonempty := by
  obtain ⟨x, hx⟩ := (preSphere_isConnected (D.flow.event T hT) i).nonempty
  obtain ⟨y, hy⟩ := retainedPreRoot_subset_parent I (rootCap_preSphere_subset I i hi hx)
  refine ⟨y, ?_⟩
  change I.parent.inclusion y ∈ (D.flow.event T hT).limit_identify.inverse ''
    ((D.flow.event T hT).necks i).neck.central_sphere
  exact hy.symm ▸ hx

theorem rootCap_parentSphere_separating (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) : SeparatingSphere (parentSphere I i) :=
  I.separating i (rootCap_parentSphere_nonempty I i hi)

theorem rootCap_parentSphere_subset_frontier (i : Fin (D.flow.event T hT).cap_count)
    (hi : i ∈ rootCaps I) : parentSphere I i ⊆ frontier (retainedRoot I) := by
  intro x hx
  have hxroot : x ∈ retainedRoot I := rootCap_preSphere_subset I i hi hx
  apply (mem_frontier_iff_notMem_interior hxroot).mpr
  rw [← retained_eq_interior_root I]
  intro hret
  have hboundary : I.parent.inclusion x ∈ frontier (D.flow.event T hT).retained_pre := by
    rw [(D.flow.event T hT).pre_boundary]
    exact mem_iUnion.mpr ⟨i, hx⟩
  exact (mem_frontier_iff_notMem_interior
    (interior_subset (I.retained_subset x hret))).mp hboundary (I.retained_subset x hret)

theorem frontier_retainedRoot :
    frontier (retainedRoot I) = ⋃ i ∈ rootCaps I, parentSphere I i := by
  apply subset_antisymm
  · intro x hx
    have hxroot := (retainedRoot_isClosed I).frontier_subset hx
    have hxdata := (mem_retainedPreRoot_iff (D.flow.event T hT) I.child
      (I.parent.inclusion x)).mp hxroot
    have hnret : x ∉ I.retained := by
      rw [retained_eq_interior_root I]
      exact (mem_frontier_iff_notMem_interior hxroot).mp hx
    have hprefront : I.parent.inclusion x ∈
        frontier (D.flow.event T hT).retained_pre := by
      apply (mem_frontier_iff_notMem_interior hxdata.1).mpr
      intro hi
      apply hnret
      rw [I.retained_eq]
      exact ⟨hi, hxdata.2⟩
    rw [(D.flow.event T hT).pre_boundary] at hprefront
    obtain ⟨i, hi⟩ := mem_iUnion.mp hprefront
    have hrootcap : i ∈ rootCaps I :=
      ⟨(D.flow.event T hT).retention.map (I.parent.inclusion x),
        (retention_mem_cap_iff (D.flow.event T hT) i hxdata.1).mpr hi, hxdata.2⟩
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hrootcap, hi⟩⟩
  · rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := mem_iUnion.mp hi
    exact rootCap_parentSphere_subset_frontier I i hi hx

theorem parentSphere_disjoint (i j : Fin (D.flow.event T hT).cap_count)
    (hij : i ≠ j) : Disjoint (parentSphere I i) (parentSphere I j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  obtain ⟨y, hy, hyx⟩ := hi
  obtain ⟨z, hz, hzx⟩ := hj
  have hyz := congrArg (D.flow.event T hT).limit_identify.map (hyx.trans hzx.symm)
  rw [(D.flow.event T hT).limit_identify.right_inverse (mem_univ y),
    (D.flow.event T hT).limit_identify.right_inverse (mem_univ z)] at hyz
  exact Set.disjoint_left.mp ((D.flow.event T hT).neck_carrier_disjoint i j hij)
    (((D.flow.event T hT).necks i).neck.central_sphere_subset hy)
    (hyz.symm ▸ ((D.flow.event T hT).necks j).neck.central_sphere_subset hz)

end ParentRoot

end PoincareConjecture.M39
