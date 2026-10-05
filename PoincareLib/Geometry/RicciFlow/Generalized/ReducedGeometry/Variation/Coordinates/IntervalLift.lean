import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.Spacetime.Rescaling.Interval.Smooth

/-!
# Smooth lifts into the selected time intervals

Morgan-Tian Definition 3.38 and Lemma 6.4, pp. 61, 107-108. M13's
interval-chart extension transfers actual real-valued inclusion
smoothness to the selected interval, including at boundary points.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M14

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (IM : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {I : SpacetimeInterval} (D : SmoothSpacetimeInterval I)

/-- Smoothness of the actual time inclusion implies smoothness into the
selected interval within any source set, Definition 3.38 and the local
coordinate argument of Lemma 6.4, pp. 61, 107-108. -/
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

/-- A time-valued map smooth after the actual inclusion is smooth into
the supplied interval on the same set, Definition 3.38 and Lemma 6.4,
pp. 61, 107-108. -/
theorem intervalLift_contMDiffOn {f : M → D.Point} {S : Set M}
    (hf : ContMDiffOn IM (𝓘(ℝ, ℝ)) ∞ (fun y => (f y : ℝ)) S) :
    ContMDiffOn IM (𝓡∂ 1) ∞ f S :=
  fun x hx => intervalLift_contMDiffWithinAt IM D (hf x hx)

end PoincareMT.M14
