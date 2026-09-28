import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.InnerParallel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.ExhaustionFunction








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff ENNReal

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M] [ProperSpace M]



theorem infDist_compl_horoball_eq_sub_exhaustion
    (hsegments : HasMinimizingSegments M) {p x : M} {c : ℝ}
    (hne : (horoballIntersection p c)ᶜ.Nonempty)
    (hx : busemannExhaustion p x ≤ c) (hpos : 0 < busemannExhaustion p x) :
    infDist x (horoballIntersection p c)ᶜ = c - busemannExhaustion p x := by
  let f := busemannExhaustion p x
  have hc : 0 ≤ c := hpos.le.trans hx
  have hxC : x ∈ horoballIntersection p c := (busemannExhaustion_le_iff hc).mp hx
  have hlower : c - f ≤ infDist x (horoballIntersection p c)ᶜ := by
    apply le_infDist_compl_of_busemann hne
    intro ray hray hray0
    have h := neg_busemann_le_exhaustion hray hray0 x
    change -busemann ray x ≤ f at h
    linarith
  apply le_antisymm ?_ hlower
  by_contra hnot
  have hlarge : c - f < infDist x (horoballIntersection p c)ᶜ := lt_of_not_ge hnot
  let e := min (f / 2) ((infDist x (horoballIntersection p c)ᶜ - (c - f)) / 2)
  have he : 0 < e := lt_min (half_pos hpos) (half_pos (sub_pos.mpr hlarge))
  have hef : e ≤ f / 2 := min_le_left _ _
  have hed : e ≤ (infDist x (horoballIntersection p c)ᶜ - (c - f)) / 2 :=
    min_le_right _ _
  have hdepth : c - f + e ≤ infDist x (horoballIntersection p c)ᶜ := by linarith
  have hparallel := innerParallelSet_eq_shift hsegments p c hne
    (show 0 ≤ c - f + e by change f ≤ c at hx; linarith)
  have hxsmall : x ∈ horoballIntersection p (f - e) := by
    have h := hparallel ▸ (show x ∈ {y ∈ horoballIntersection p c |
      c - f + e ≤ infDist y (horoballIntersection p c)ᶜ} from ⟨hxC, hdepth⟩)
    convert h using 1 <;> ring
  have h := (busemannExhaustion_le_iff (show 0 ≤ f - e by linarith)).mpr hxsmall
  change f ≤ f - e at h
  linarith

end Poincare.Riemannian.Soul

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem infDist_frontier_eq_infDist_compl
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {C : Set M} (hC : IsClosed C) (hfront : (frontier C).Nonempty)
    (hcompl : Cᶜ.Nonempty) {x : M} (hx : x ∈ C) :
    letI := g.toMetricSpace
    infDist x (frontier C) = infDist x Cᶜ := by
  letI := g.toMetricSpace
  apply le_antisymm
  · apply (le_infDist hcompl).2
    exact (g.le_frontier_dist_iff_le_compl_dist hc hC hx).1
      (fun y hy => infDist_le_dist_of_mem hy)
  · apply (le_infDist hfront).2
    exact (g.le_frontier_dist_iff_le_compl_dist hc hC hx).2
      (fun y hy => infDist_le_dist_of_mem hy)

end PoincareConjecture.RiemannianMetric
