import PoincareConjecture.Proofs.M11.BoxTopology





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

def sliceBoxMap (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) (x : b.spatial) : spacetimeSlice time t :=
  ⟨b.toSpacetime (⟨t, ht⟩, x), b.time_toSpacetime _⟩

theorem sliceBoxMap_range (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) :
    range (sliceBoxMap b t ht) =
      (Subtype.val : spacetimeSlice time t → X) ⁻¹' (boxHomeomorph b).target := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact (boxHomeomorph b).map_source (mem_univ _)
  · intro hp
    let q := (boxHomeomorph b).symm p.val
    have htime : q.1 = ⟨t, ht⟩ :=
      Subtype.ext ((boxHomeomorph_inverse_time b hp).trans p.property)
    refine ⟨q.2, Subtype.ext ?_⟩
    change b.toSpacetime (⟨t, ht⟩, q.2) = p.val
    rw [← htime]
    exact boxHomeomorph_right_inv b hp

theorem sliceBoxMap_openEmbedding (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) : IsOpenEmbedding (sliceBoxMap b t ht) := by
  constructor
  · apply IsEmbedding.subtypeVal.of_comp_iff.mp
    exact b.openEmbedding.isEmbedding.comp (isEmbedding_prodMkRight (⟨t, ht⟩ : b.interval.domain))
  · rw [sliceBoxMap_range]
    exact (boxHomeomorph b).open_target.preimage continuous_subtype_val

noncomputable def sliceHomeomorph (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) : OpenPartialHomeomorph b.spatial (spacetimeSlice time t) := by
  letI : Nonempty b.spatial := b.spatial_nonempty.to_subtype
  exact (sliceBoxMap_openEmbedding b t ht).toOpenPartialHomeomorph (sliceBoxMap b t ht)

theorem sliceHomeomorph_apply (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) (x : b.spatial) :
    sliceHomeomorph b t ht x = sliceBoxMap b t ht x := rfl

theorem sliceHomeomorph_source (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) : (sliceHomeomorph b t ht).source = univ := rfl

theorem sliceHomeomorph_target (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) :
    (sliceHomeomorph b t ht).target =
      (Subtype.val : spacetimeSlice time t → X) ⁻¹' (boxHomeomorph b).target := by
  rw [← sliceBoxMap_range b t ht]
  simp [sliceHomeomorph]

theorem sliceHomeomorph_inverse (b : AdaptedMetricBox n X time I) (t : ℝ)
    (ht : t ∈ b.interval.domain) (p : spacetimeSlice time t)
    (hp : p ∈ (sliceHomeomorph b t ht).target) :
    (sliceHomeomorph b t ht).symm p = ((boxHomeomorph b).symm p.val).2 := by
  have h := congrArg Subtype.val ((sliceHomeomorph b t ht).right_inv hp)
  change b.toSpacetime (⟨t, ht⟩, (sliceHomeomorph b t ht).symm p) = p.val at h
  have hq := congrArg (fun q : boxDomain b ↦ q.2)
    (congrArg (boxHomeomorph b).symm h)
  rw [boxHomeomorph_left_inv] at hq
  exact hq

theorem slice_targets_cover (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) :
    ∃ b : {b : A.box_index // t ∈ (A.box b).interval.domain},
      p ∈ (sliceHomeomorph (A.box b.val) t b.property).target := by
  obtain ⟨b, q, hq⟩ := A.box_covers p.val
  have ht : q.1.val = t := ((A.box b).time_toSpacetime q).symm.trans
    ((congrArg A.time hq).trans p.property)
  refine ⟨⟨b, ht ▸ q.1.property⟩, ?_⟩
  rw [sliceHomeomorph_target]
  change p.val ∈ (boxHomeomorph (A.box b)).target
  rw [← hq]
  exact (boxHomeomorph (A.box b)).map_source (mem_univ q)

end PoincareConjecture.Proofs.M11
