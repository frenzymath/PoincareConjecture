import PoincareConjecture.Proofs.M11.SliceLabelDifferential
import PoincareConjecture.Proofs.M11.SliceCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem sliceLabelHomeomorph_box (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial) :
    sliceLabelHomeomorph (L.slice t) (L.boxMap b t ht x) =
      sliceBoxMap (A.box b) t ht x :=
  Subtype.ext (L.boxMap_eq b t ht x)

theorem sliceLabelHomeomorph_smooth (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sliceLabelHomeomorph (L.slice t)) := by
  let := adaptedSliceChartedSpace A t
  intro p
  obtain ⟨b, hp⟩ := labelBox_targets_cover A L t p
  have hi := (labelBox_inverse_smooth A L b.val t b.property).contMDiffAt
    ((labelBoxHomeomorph A L b.val t b.property).open_target.mem_nhds hp)
  have hs := (adapted_sliceBox_localDiffeomorph A b.val t b.property).contMDiff
  apply (hs.contMDiffAt.comp p hi).congr_of_eventuallyEq
  filter_upwards [(labelBoxHomeomorph A L b.val t b.property).open_target.mem_nhds hp]
    with q hq
  change sliceLabelHomeomorph (L.slice t) q =
    sliceBoxMap (A.box b.val) t b.property ((labelBoxHomeomorph A L b.val t b.property).symm q)
  rw [← sliceLabelHomeomorph_box]
  congr 1
  rw [← labelBoxHomeomorph_apply,
    (labelBoxHomeomorph A L b.val t b.property).right_inv hq]

theorem sliceLabelHomeomorph_inverse_smooth (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sliceLabelHomeomorph (L.slice t)).symm := by
  let := adaptedSliceChartedSpace A t
  apply (cover_smooth_iff
    (fun b : {b : A.box_index // t ∈ (A.box b).interval.domain} ↦
      sliceHomeomorph (A.box b.val) t b.property) (slice_targets_cover A t)
      (slice_transition_smooth A t) _).mpr
  intro b
  have heq : (sliceLabelHomeomorph (L.slice t)).symm ∘
      sliceHomeomorph (A.box b.val) t b.property = L.boxMap b.val t b.property :=
    funext (labelBoxHomeomorph_apply A L b.val t b.property)
  rw [heq]
  exact (L.boxMap_smooth b.val t b.property).contMDiffOn

noncomputable def sliceLabelDiffeomorph (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    Diffeomorph (𝓡 n) (𝓡 n) (L.slice t).carrier (spacetimeSlice A.time t) ∞ :=
  letI := adaptedSliceChartedSpace A t
  {
    toEquiv := (sliceLabelHomeomorph (L.slice t)).toEquiv
    contMDiff_toFun := sliceLabelHomeomorph_smooth A L t
    contMDiff_invFun := sliceLabelHomeomorph_inverse_smooth A L t
  }

end PoincareConjecture.Proofs.M11
