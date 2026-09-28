import PoincareConjecture.Proofs.M11.SliceTopology
import PoincareConjecture.Proofs.M11.BoxTransitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem slice_transition_smooth (A : AdaptedMetricAtlas n X) (t : ℝ)
    (b c : {b : A.box_index // t ∈ (A.box b).interval.domain}) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞
      ((sliceHomeomorph (A.box b.val) t b.property).trans
        (sliceHomeomorph (A.box c.val) t c.property).symm)
      ((sliceHomeomorph (A.box b.val) t b.property).trans
        (sliceHomeomorph (A.box c.val) t c.property).symm).source := by
  let := intervalChartedSpace (A.box b.val).interval
  let := intervalChartedSpace (A.box c.val).interval
  intro x hx
  have htarget : (A.box b.val).toSpacetime (⟨t, b.property⟩, x) ∈
      (boxHomeomorph (A.box c.val)).target := by
    have h := hx.2
    change sliceHomeomorph (A.box b.val) t b.property x ∈
      (sliceHomeomorph (A.box c.val) t c.property).target at h
    rw [sliceHomeomorph_target] at h
    exact h
  have hfixed : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : (A.box b.val).spatial ↦ ((⟨t, b.property⟩ : (A.box b.val).interval.domain), y)) :=
    contMDiff_const.prodMk contMDiff_id
  have htransition := (box_transition_smooth A b.val c.val).contMDiffAt
    (((boxHomeomorph (A.box b.val)).trans (boxHomeomorph (A.box c.val)).symm).open_source.mem_nhds
      ⟨mem_univ _, htarget⟩)
  have hlocal := contMDiffAt_snd.comp x (htransition.comp x (hfixed x))
  apply ContMDiffAt.contMDiffWithinAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [((sliceHomeomorph (A.box b.val) t b.property).trans
    (sliceHomeomorph (A.box c.val) t c.property).symm).open_source.mem_nhds hx] with y hy
  exact sliceHomeomorph_inverse (A.box c.val) t c.property
    (sliceHomeomorph (A.box b.val) t b.property y) hy.2

noncomputable abbrev adaptedSliceChartedSpace (A : AdaptedMetricAtlas n X) (t : ℝ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (spacetimeSlice A.time t) :=
  coverChartedSpace (H := EuclideanSpace ℝ (Fin n))
    (fun b : {b : A.box_index // t ∈ (A.box b).interval.domain} ↦
      sliceHomeomorph (A.box b.val) t b.property) (slice_targets_cover A t)

theorem adaptedSlice_isManifold (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedSliceChartedSpace A t
    IsManifold (𝓡 n) ∞ (spacetimeSlice A.time t) :=
  cover_isManifold
    (fun b : {b : A.box_index // t ∈ (A.box b).interval.domain} ↦
      sliceHomeomorph (A.box b.val) t b.property) (slice_targets_cover A t)
    (slice_transition_smooth A t)

theorem adapted_sliceBox_localDiffeomorph (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (t : ℝ) (ht : t ∈ (A.box b).interval.domain) :
    letI := adaptedSliceChartedSpace A t
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (sliceBoxMap (A.box b) t ht) :=
  cover_localDiffeomorph
    (fun b : {b : A.box_index // t ∈ (A.box b).interval.domain} ↦
      sliceHomeomorph (A.box b.val) t b.property) (slice_targets_cover A t)
    (slice_transition_smooth A t) ⟨b, ht⟩ (sliceHomeomorph_source (A.box b) t ht)

theorem slice_inclusion_smooth (A : AdaptedMetricAtlas n X) (t : ℝ) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (Subtype.val : spacetimeSlice A.time t → X) := by
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  apply (cover_smooth_iff
    (fun b : {b : A.box_index // t ∈ (A.box b).interval.domain} ↦
      sliceHomeomorph (A.box b.val) t b.property) (slice_targets_cover A t)
      (slice_transition_smooth A t) _).mpr
  intro b
  let := intervalChartedSpace (A.box b.val).interval
  exact ((adapted_box_localDiffeomorph A b.val).contMDiff.comp
    (contMDiff_const.prodMk contMDiff_id)).contMDiffOn

end PoincareConjecture.Proofs.M11
