import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.SpatialMetricCoefficients
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic

/-!
# Smooth actual metric at the meeting endpoint

Morgan-Tian Proposition 6.30, pp. 118-119. Fixing an actual allowed
gauge time gives a smooth metric coefficient in the spatial endpoint,
including when that time is a physical boundary.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- The actual fixed-time metric coefficient is smooth at every gauge
point, the positive momentum used in Proposition 6.30, pp. 118-119. -/
theorem meetingMetric_contDiffAt (j : G.gaugeCover.index)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (q : G.gaugeCover.spatial j) :
    ContDiffAt ℝ ∞
      (fun y => Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric j).metric q (t.val, y))
      q.val := by
  have hm := Proofs.M11.ordinaryChartMetric_smooth (G.gaugeCover.metric j).metric
    (G.gaugeCover.interval j).domain (G.gaugeCover.metric j).smooth q
  have h : ContDiffOn ℝ ∞
      (fun y => Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric j).metric q (t.val, y))
      (G.gaugeCover.spatial j : Set _) := by
    apply hm.comp (contDiffOn_const.prodMk contDiffOn_id)
    intro y hy
    refine ⟨t.property, ?_⟩
    change y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target
    rw [(G.gaugeCover.spatial j).chartAt_target_eq]
    exact hy
  exact (h q.val q.property).contDiffAt ((G.gaugeCover.spatial j).isOpen.mem_nhds q.property)

end PoincareMT.M14
