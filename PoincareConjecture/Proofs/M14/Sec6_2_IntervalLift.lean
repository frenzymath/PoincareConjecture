import PoincareConjecture.Proofs.M13.IntervalSmooth









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M14

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (IM : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {I : SpacetimeInterval} (D : SmoothSpacetimeInterval I)




theorem intervalLift_contMDiffWithinAt {f : M → D.Point} {S : Set M} {x : M}
    (hf : ContMDiffWithinAt IM (𝓘(ℝ, ℝ)) ∞ (fun y => (f y : ℝ)) S x) :
    ContMDiffWithinAt IM (𝓡∂ 1) ∞ f S x := by
  have hc : ContinuousWithinAt f S x :=
    Topology.IsEmbedding.subtypeVal.isInducing.continuousWithinAt_iff.mpr hf.continuousWithinAt
  rw [contMDiffWithinAt_iff_target]
  refine ⟨hc, ?_⟩
  let e := extChartAt (𝓡∂ 1) (f x)
  have hU : f ⁻¹' e.source ∈ 𝓝[S] x :=
    hc.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x))
  have hchart := (M13.intervalChartExtension_contDiffOn D (f x)).contMDiffOn
    (f x : ℝ) ⟨f x, mem_extChartAt_source (f x), rfl⟩
  have hcomp := hchart.comp x (hf.mono inter_subset_left)
    (show MapsTo (fun y => (f y : ℝ)) (S ∩ f ⁻¹' e.source)
      ((Subtype.val : D.Point → ℝ) '' e.source) from fun y hy => ⟨f y, hy.2, rfl⟩)
  have hpoint := hcomp.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hU)
  simpa only [Function.comp_def, M13.intervalChartExtension_val] using hpoint




theorem intervalLift_contMDiffOn {f : M → D.Point} {S : Set M}
    (hf : ContMDiffOn IM (𝓘(ℝ, ℝ)) ∞ (fun y => (f y : ℝ)) S) :
    ContMDiffOn IM (𝓡∂ 1) ∞ f S :=
  fun x hx => intervalLift_contMDiffWithinAt IM D (hf x hx)

end PoincareConjecture.M14
