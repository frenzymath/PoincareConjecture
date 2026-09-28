import PoincareConjecture.Proofs.M14.Sec6_2_SpatialMetricCoefficients
import PoincareConjecture.Definitions.M14GeneralizedLGeometry

set_option autoImplicit false

open Set
open scoped ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

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

end PoincareConjecture.M14
