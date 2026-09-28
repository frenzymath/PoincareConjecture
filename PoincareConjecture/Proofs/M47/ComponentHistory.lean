import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.M47

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem capFree_post_component_subset_interior
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    connectedComponent x ⊆ interior E.retained_post := by
  let : LocallyConnectedSpace (slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice T).carrier
  apply isOpen_connectedComponent.subset_interior_iff.2
  intro y hy
  have hcover : y ∈ E.retained_post ∪ (⋃ i, (E.caps i).carrier) := by
    rw [E.post_cover]
    exact mem_univ y
  apply hcover.resolve_right
  intro hcap
  obtain ⟨i, hi⟩ := mem_iUnion.1 hcap
  exact Set.disjoint_left.1 (hfree i) hy hi

theorem capFree_inverse_component_subset_interior
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    E.retention.inverse '' connectedComponent x ⊆ interior E.retained_pre := by
  rintro y ⟨z, hz, rfl⟩
  have hzret := interior_subset (capFree_post_component_subset_interior E hfree hz)
  have hyret : E.retention.inverse z ∈ E.retained_pre :=
    E.retention.inverse_image.subset ⟨z, hzret, rfl⟩
  by_contra hnot
  have hfront : E.retention.inverse z ∈ frontier E.retained_pre :=
    (mem_frontier_iff_notMem_interior hyret).2 hnot
  rw [E.pre_boundary] at hfront
  obtain ⟨i, hi⟩ := mem_iUnion.1 hfront
  have hpostfront : z ∈ frontier (E.caps i).carrier := by
    rw [← E.boundary_correspondence i]
    exact ⟨E.retention.inverse z, hi, E.retention.right_inverse hzret⟩
  have hcap : z ∈ (E.caps i).carrier :=
    (E.caps i).carrier_compact.isClosed.closure_eq ▸ frontier_subset_closure hpostfront
  exact Set.disjoint_left.1 (hfree i) hz hcap

theorem capFree_inverse_image_component
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    E.retention.inverse '' connectedComponent x =
      connectedComponent (E.retention.inverse x) := by
  let : LocallyConnectedSpace (slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice T).carrier
  have hpost : connectedComponent x ⊆ E.retained_post :=
    (capFree_post_component_subset_interior E hfree).trans interior_subset
  have hpre := capFree_inverse_component_subset_interior E hfree
  have hset : E.retention.inverse '' connectedComponent x =
      interior E.retained_pre ∩ E.retention.map ⁻¹' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hpre ⟨z, hz, rfl⟩, by
        simpa only [mem_preimage, E.retention.right_inverse (hpost hz)] using hz⟩
    · rintro ⟨hy, hmap⟩
      exact ⟨E.retention.map y, hmap, E.retention.left_inverse (interior_subset hy)⟩
  have hopen : IsOpen (E.retention.inverse '' connectedComponent x) := by
    rw [hset]
    exact (E.retention.map_smooth.continuousOn.mono interior_subset).isOpen_inter_preimage
      isOpen_interior isOpen_connectedComponent
  have hcontinuous := E.retention.inverse_smooth.continuousOn.mono hpost
  have hcompact := hC.image_of_continuousOn hcontinuous
  have hconnected := (isConnected_connectedComponent (x := x)).image
    E.retention.inverse hcontinuous
  have hpoint : E.retention.inverse x ∈ E.retention.inverse '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  exact Set.Subset.antisymm (hconnected.subset_connectedComponent hpoint)
    ((show IsClopen _ from ⟨hcompact.isClosed, hopen⟩).connectedComponent_subset hpoint)

theorem capFree_pre_component_subset_interior
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    connectedComponent (E.retention.inverse x) ⊆ interior E.retained_pre := by
  rw [← capFree_inverse_image_component E hC hfree]
  exact capFree_inverse_component_subset_interior E hfree

theorem capFree_pre_component_compact
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    IsCompact (connectedComponent (E.retention.inverse x)) := by
  rw [← capFree_inverse_image_component E hC hfree]
  exact hC.image_of_continuousOn (E.retention.inverse_smooth.continuousOn.mono
    ((capFree_post_component_subset_interior E hfree).trans interior_subset))

theorem capFree_limit_image_component
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    E.limit_identify.map '' connectedComponent (E.retention.inverse x) =
      connectedComponent (E.limit_identify.map (E.retention.inverse x)) := by
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice E.tMinus).carrier
  have hpre : connectedComponent (E.retention.inverse x) ⊆ E.regular_limit :=
    ((capFree_pre_component_subset_interior E hC hfree).trans interior_subset).trans
      E.retained_pre_subset
  have hset : E.limit_identify.map '' connectedComponent (E.retention.inverse x) =
      E.limit_identify.inverse ⁻¹' connectedComponent (E.retention.inverse x) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [mem_preimage, E.limit_identify.left_inverse (hpre hz)] using hz
    · intro hy
      exact ⟨E.limit_identify.inverse y, hy, E.limit_identify.right_inverse (mem_univ y)⟩
  have hopen : IsOpen
      (E.limit_identify.map '' connectedComponent (E.retention.inverse x)) := by
    rw [hset]
    exact isOpen_connectedComponent.preimage
      (continuousOn_univ.1 E.limit_identify.inverse_smooth.continuousOn)
  have hcontinuous := E.limit_identify.map_smooth.continuousOn.mono hpre
  have hcompact := (capFree_pre_component_compact E hC hfree).image_of_continuousOn hcontinuous
  have hconnected := (isConnected_connectedComponent (x := E.retention.inverse x)).image
    E.limit_identify.map hcontinuous
  have hpoint : E.limit_identify.map (E.retention.inverse x) ∈
      E.limit_identify.map '' connectedComponent (E.retention.inverse x) :=
    ⟨E.retention.inverse x, mem_connectedComponent, rfl⟩
  exact Set.Subset.antisymm (hconnected.subset_connectedComponent hpoint)
    ((show IsClopen _ from ⟨hcompact.isClosed, hopen⟩).connectedComponent_subset hpoint)

def capFreeComponentEquivalence
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    SurgeryRegionEquivalence (slice E.tMinus) (slice T)
      (connectedComponent (E.retention.inverse x)) (connectedComponent x) := by
  have hpre : connectedComponent (E.retention.inverse x) ⊆ E.retained_pre :=
    (capFree_pre_component_subset_interior E hC hfree).trans interior_subset
  have hpost : connectedComponent x ⊆ E.retained_post :=
    (capFree_post_component_subset_interior E hfree).trans interior_subset
  refine {
    map := E.retention.map
    inverse := E.retention.inverse
    map_image := ?_
    inverse_image := capFree_inverse_image_component E hC hfree
    left_inverse := fun _ hy => E.retention.left_inverse (hpre hy)
    right_inverse := fun _ hy => E.retention.right_inverse (hpost hy)
    map_smooth := E.retention.map_smooth.mono hpre
    inverse_smooth := E.retention.inverse_smooth.mono hpost
  }
  rw [← capFree_inverse_image_component E hC hfree]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simpa only [E.retention.right_inverse (hpost hw)] using hw
  · intro hy
    exact ⟨E.retention.inverse y, ⟨y, hy, rfl⟩, E.retention.right_inverse (hpost hy)⟩

theorem capFree_terminal_inverse_image_component
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    E.limit_identify.inverse ''
        connectedComponent (E.limit_identify.map (E.retention.inverse x)) =
      connectedComponent (E.retention.inverse x) := by
  have hpre : connectedComponent (E.retention.inverse x) ⊆ E.regular_limit :=
    ((capFree_pre_component_subset_interior E hC hfree).trans interior_subset).trans
      E.retained_pre_subset
  rw [← capFree_limit_image_component E hC hfree]
  ext y
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simpa only [E.limit_identify.left_inverse (hpre hw)] using hw
  · intro hy
    exact ⟨E.limit_identify.map y, ⟨y, hy, rfl⟩, E.limit_identify.left_inverse (hpre hy)⟩

theorem capFree_terminal_component_compact
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    IsCompact (connectedComponent (E.limit_identify.map (E.retention.inverse x))) := by
  have hpre : connectedComponent (E.retention.inverse x) ⊆ E.regular_limit :=
    ((capFree_pre_component_subset_interior E hC hfree).trans interior_subset).trans
      E.retained_pre_subset
  rw [← capFree_limit_image_component E hC hfree]
  exact (capFree_pre_component_compact E hC hfree).image_of_continuousOn
    (E.limit_identify.map_smooth.continuousOn.mono hpre)

def capFreeTerminalComponentEquivalence
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier) :
    SurgeryRegionEquivalence E.terminal (slice T)
      (connectedComponent (E.limit_identify.map (E.retention.inverse x)))
      (connectedComponent x) := by
  have hpre : connectedComponent (E.retention.inverse x) ⊆ E.retained_pre :=
    (capFree_pre_component_subset_interior E hC hfree).trans interior_subset
  have hpost : connectedComponent x ⊆ E.retained_post :=
    (capFree_post_component_subset_interior E hfree).trans interior_subset
  have htermPre : MapsTo E.limit_identify.inverse
      (connectedComponent (E.limit_identify.map (E.retention.inverse x)))
      (connectedComponent (E.retention.inverse x)) := by
    intro y hy
    exact (capFree_terminal_inverse_image_component E hC hfree).subset ⟨y, hy, rfl⟩
  have hpostPre : MapsTo E.retention.inverse (connectedComponent x)
      (connectedComponent (E.retention.inverse x)) := by
    intro y hy
    exact (capFree_inverse_image_component E hC hfree).subset ⟨y, hy, rfl⟩
  refine {
    map := E.retention.map ∘ E.limit_identify.inverse
    inverse := E.limit_identify.map ∘ E.retention.inverse
    map_image := ?_
    inverse_image := ?_
    left_inverse := ?_
    right_inverse := ?_
    map_smooth := ?_
    inverse_smooth := ?_
  }
  · change (fun z => E.retention.map (E.limit_identify.inverse z)) '' _ = _
    rw [← image_image E.retention.map E.limit_identify.inverse,
      capFree_terminal_inverse_image_component E hC hfree]
    exact (capFreeComponentEquivalence E hC hfree).map_image
  · change (fun z => E.limit_identify.map (E.retention.inverse z)) '' _ = _
    rw [← image_image E.limit_identify.map E.retention.inverse,
      capFree_inverse_image_component E hC hfree,
      capFree_limit_image_component E hC hfree]
  · intro y hy
    simp only [Function.comp_apply, E.retention.left_inverse (hpre (htermPre hy)),
      E.limit_identify.right_inverse (mem_univ y)]
  · intro y hy
    simp only [Function.comp_apply,
      E.limit_identify.left_inverse (E.retained_pre_subset (hpre (hpostPre hy))),
      E.retention.right_inverse (hpost hy)]
  · exact E.retention.map_smooth.comp
      (E.limit_identify.inverse_smooth.mono (subset_univ _))
      (fun _ hy => hpre (htermPre hy))
  · exact E.limit_identify.map_smooth.comp
      (E.retention.inverse_smooth.mono hpost)
      (fun _ hy => E.retained_pre_subset (hpre (hpostPre hy)))

theorem capFree_terminal_component_metric
    (E : SurgeryEventData g₀ K P slice metric T) {x : (slice T).carrier}
    (hC : IsCompact (connectedComponent x))
    (hfree : ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier)
    (z : E.terminal.carrier)
    (hz : z ∈ connectedComponent (E.limit_identify.map (E.retention.inverse x)))
    (v w : TangentSpace (𝓡 3) z) :
    (metric T).inner (E.retention.map (E.limit_identify.inverse z))
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ E.limit_identify.inverse) z v)
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ E.limit_identify.inverse) z w) =
        E.limit_metric.inner z v w := by
  have hzpre := (capFree_terminal_inverse_image_component E hC hfree).subset ⟨z, hz, rfl⟩
  have hzint := capFree_pre_component_subset_interior E hC hfree hzpre
  have hzret := interior_subset hzint
  have hzregular := E.retained_pre_subset hzret
  have hg : MDifferentiableAt (𝓡 3) (𝓡 3) E.limit_identify.inverse z :=
    (contMDiffOn_univ.1 E.limit_identify.inverse_smooth).mdifferentiable (by simp) z
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) E.limit_identify.map
      (E.limit_identify.inverse z) :=
    (E.limit_identify.map_smooth.contMDiffAt
      (E.regular_limit_open.mem_nhds hzregular)).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 3) (𝓡 3) E.retention.map
      (E.limit_identify.inverse z) :=
    (E.retention.map_smooth.contMDiffAt
      (mem_interior_iff_mem_nhds.1 hzint)).mdifferentiableAt (by simp)
  have hcomp : E.limit_identify.map ∘ E.limit_identify.inverse = id := by
    funext y
    exact E.limit_identify.right_inverse (mem_univ y)
  have hd := mfderiv_comp z hf hg
  rw [hcomp, mfderiv_id] at hd
  have hvector (q : TangentSpace (𝓡 3) z) :
      mfderiv (𝓡 3) (𝓡 3) E.limit_identify.map (E.limit_identify.inverse z)
        (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z q) = q :=
    (congrArg (fun A => A q) hd).symm
  have hmetric := E.retained_metric (E.limit_identify.inverse z) hzret
    (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z v)
    (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z w)
  rw [hvector v, hvector w, E.limit_identify.right_inverse (mem_univ z)] at hmetric
  simpa only [mfderiv_comp z ha hg, ContinuousLinearMap.comp_apply] using hmetric

end PoincareConjecture.M47
