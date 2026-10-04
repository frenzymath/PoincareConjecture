import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckVolumeCharts

/-!
# A fixed finite coordinate cover of a buffered model cylinder

The model cover is chosen before any source manifold, metric or neck.
This fixes the number of charts in the uniform upper-volume estimate
used in Morgan--Tian Theorem 5.6, pp. 85-87, and Claims 10.7-10.10.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M28

private abbrev E := EuclideanSpace ℝ (Fin 3)

/-- Every fixed finite model slab has a finite cover by the actual model
coordinate unit balls, with each chart centered in that same slab. The
choice is independent of all source-neck geometry. -/
theorem exists_neckVolumeModelChart_finite_cover (S : ℝ) :
    ∃ t : Finset (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace),
      (univ ×ˢ Icc (-2 * S) (2 * S) : Set RoundCylinderSpace) ⊆
        ⋃ z ∈ t, neckVolumeModelChart z.val.1 z.val.2 '' Metric.ball (0 : E) 1 := by
  let K : Set RoundCylinderSpace := univ ×ˢ Icc (-2 * S) (2 * S)
  let U (z : K) : Set RoundCylinderSpace :=
    neckVolumeModelChart z.val.1 z.val.2 '' Metric.ball (0 : E) 1
  have hU (z : K) : IsOpen (U z) := by
    apply (neckVolumeModelChart z.val.1 z.val.2).isOpen_image_of_subset_source
      Metric.isOpen_ball
    rw [neckVolumeModelChart_source]
    exact subset_univ _
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    apply mem_iUnion.mpr
    refine ⟨⟨z, hz⟩, 0, by simp, ?_⟩
    exact neckVolumeModelChart_zero z.1 z.2
  exact (isCompact_univ.prod isCompact_Icc).elim_finite_subcover U hU hcover

end PoincareMT.M28
