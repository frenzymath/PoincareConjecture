import PoincareConjecture.Proofs.M11.SliceCharts
import PoincareConjecture.Proofs.M11.BoxInverseDifferential





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_slice_of_inclusion (A : AdaptedMetricAtlas n X) (t : ℝ)
    (f : M → spacetimeSlice A.time t) (x : M) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    ContMDiffAt J (spacetimeModel n) ∞ (Subtype.val ∘ f) x →
      ContMDiffAt J (𝓡 n) ∞ f x := by
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  intro hf
  obtain ⟨b, hb⟩ := slice_targets_cover A t (f x)
  let := intervalChartedSpace (A.box b.val).interval
  have hp : (f x).val ∈ (boxHomeomorph (A.box b.val)).target := by
    rw [sliceHomeomorph_target] at hb
    exact hb
  have hi := ((box_inverse_smooth A b.val).contMDiffAt
    ((boxHomeomorph (A.box b.val)).open_target.mem_nhds hp)).snd.comp x hf
  have hs := (adapted_sliceBox_localDiffeomorph A b.val t b.property).contMDiff
  apply (hs.contMDiffAt.comp x hi).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.preimage_mem_nhds
    ((boxHomeomorph (A.box b.val)).open_target.mem_nhds hp)] with y hy
  have ht : ((boxHomeomorph (A.box b.val)).symm (f y).val).1 = ⟨t, b.property⟩ :=
    Subtype.ext ((boxHomeomorph_inverse_time (A.box b.val) hy).trans (f y).property)
  apply Subtype.ext
  change (f y).val = (A.box b.val).toSpacetime
    (⟨t, b.property⟩, ((boxHomeomorph (A.box b.val)).symm (f y).val).2)
  rw [← ht]
  exact (boxHomeomorph_right_inv (A.box b.val) hy).symm

theorem contMDiff_slice_iff (A : AdaptedMetricAtlas n X) (t : ℝ)
    (f : M → spacetimeSlice A.time t) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    ContMDiff J (𝓡 n) ∞ f ↔ ContMDiff J (spacetimeModel n) ∞ (Subtype.val ∘ f) := by
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  exact ⟨fun hf ↦ (slice_inclusion_smooth A t).comp hf,
    fun hf x ↦ contMDiffAt_slice_of_inclusion A t f x (hf x)⟩

end PoincareConjecture.Proofs.M11
