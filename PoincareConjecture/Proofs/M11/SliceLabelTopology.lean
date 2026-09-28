import PoincareConjecture.Proofs.M11.SliceTopology
import PoincareConjecture.Definitions.M11SpacetimeSlices





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {time : X → ℝ} {t : ℝ}

def sliceLabelMap (L : SpacetimeSliceLabel n X time t) (x : L.carrier) :
    spacetimeSlice time t := ⟨L.toSpacetime x, L.time_eq x⟩

theorem sliceLabelMap_embedding (L : SpacetimeSliceLabel n X time t) :
    IsEmbedding (sliceLabelMap L) :=
  IsEmbedding.subtypeVal.of_comp_iff.mp L.embedding

theorem sliceLabelMap_surjective (L : SpacetimeSliceLabel n X time t) :
    Function.Surjective (sliceLabelMap L) := by
  intro p
  obtain ⟨x, hx⟩ := L.range_eq.symm ▸ (show p.val ∈ {p | time p = t} from p.property)
  exact ⟨x, Subtype.ext hx⟩

noncomputable def sliceLabelHomeomorph (L : SpacetimeSliceLabel n X time t) :
    L.carrier ≃ₜ spacetimeSlice time t :=
  (Equiv.ofBijective (sliceLabelMap L)
    ⟨(sliceLabelMap_embedding L).injective, sliceLabelMap_surjective L⟩).toHomeomorphOfIsInducing
      (sliceLabelMap_embedding L).isInducing

theorem sliceLabelHomeomorph_apply (L : SpacetimeSliceLabel n X time t) (x : L.carrier) :
    sliceLabelHomeomorph L x = sliceLabelMap L x := rfl

noncomputable def labelBoxHomeomorph (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) :
    OpenPartialHomeomorph (A.box b).spatial (L.slice t).carrier :=
  (sliceHomeomorph (A.box b) t ht).trans
    (sliceLabelHomeomorph (L.slice t)).symm.toOpenPartialHomeomorph

theorem labelBoxHomeomorph_apply (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial) :
    labelBoxHomeomorph A L b t ht x = L.boxMap b t ht x := by
  apply (sliceLabelHomeomorph (L.slice t)).injective
  change sliceLabelHomeomorph (L.slice t)
    ((sliceLabelHomeomorph (L.slice t)).symm (sliceBoxMap (A.box b) t ht x)) = _
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (L.boxMap_eq b t ht x).symm

theorem labelBoxHomeomorph_source (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) : (labelBoxHomeomorph A L b t ht).source = univ := by
  simp [labelBoxHomeomorph, sliceHomeomorph_source]

theorem labelBox_targets_cover (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (t : ℝ) (p : (L.slice t).carrier) :
    ∃ b : {b : A.box_index // t ∈ (A.box b).interval.domain},
      p ∈ (labelBoxHomeomorph A L b.val t b.property).target := by
  obtain ⟨b, hb⟩ := slice_targets_cover A t (sliceLabelHomeomorph (L.slice t) p)
  exact ⟨b, ⟨mem_univ p, hb⟩⟩

end PoincareConjecture.Proofs.M11
