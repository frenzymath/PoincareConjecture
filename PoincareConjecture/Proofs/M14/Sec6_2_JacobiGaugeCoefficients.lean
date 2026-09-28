import PoincareConjecture.Proofs.M14.Sec6_4_GaugeCoefficients
import PoincareConjecture.Proofs.M08.WeightedJacobiIdentities










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {a c : ℝ} (hac : a < c)
  (htime : ∀ s ∈ Icc a c, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
  (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ Icc a c)
  (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
  (ht : T - s ^ 2 = t.val)

private theorem gauge_extChartAt_eq_val : extChartAt (𝓡 n) x y = y.val := by
  rw [extChartAt_coe]
  rfl

private theorem gauge_chart_source : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
  rw [(G.gaugeCover.spatial b).chartAt_source_eq_univ]
  exact mem_univ y

include hCoordinates hM04 hac htime hs ht




theorem gauge_closedJacobiPotential
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise)) (A v w : EuclideanSpace ℝ (Fin n)) :
    M08.closedChartJacobiPotential W.flow T x (Icc a c) (s, y.val) A v w =
      -horizontalRiemann G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y A)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y A) +
      2 * s * M14BcalPairing G ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y A)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) +
      2 * s ^ 2 * M14HorizontalHessianPairing G
        ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) -
      4 * s * M14HorizontalRicciDerivativePairing G
        ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y A)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have hy := (extChartAt (𝓡 n) x).map_source
    (show y ∈ (extChartAt (𝓡 n) x).source from by
      simpa only [extChartAt_source] using gauge_chart_source b x y)
  have h := M08.closedChartJacobiPotential_identification W.flow hM04 T
    (uniqueDiffOn_Icc hac) htime (gauge_chart_source b x y) hs
    (M08.mem_closure_interior_Icc_prod hac (isOpen_extChartAt_target (I := 𝓡 n) x) hs hy)
    A v w
  rw [ht, (ordinaryGauge_movingCalculus b hCoordinates W).riemann_eq,
    movingGauge_bcalPairing (ordinaryGauge_movingCalculus b hCoordinates W),
    movingGauge_horizontalHessianPairing (ordinaryGauge_movingCalculus b hCoordinates W) hscalar,
    movingGauge_ricciDerivativePairing (ordinaryGauge_movingCalculus b hCoordinates W)] at h
  simpa only [openSubset_chartFrame, gauge_extChartAt_eq_val, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h




theorem gauge_chartActionMetric_timeWithin_pair (v w : EuclideanSpace ℝ (Fin n)) :
    M08.timeWithinFDeriv (Icc a c) (extChartAt (𝓡 n) x).target
        (M08.chartActionMetric W.flow T x) (s, y.val) v w =
      4 * s * horizontalRicci G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have hy := (extChartAt (𝓡 n) x).map_source
    (show y ∈ (extChartAt (𝓡 n) x).source from by
      simpa only [extChartAt_source] using gauge_chart_source b x y)
  have h := congrArg (fun L => L v w)
    (M08.chartActionMetric_timeWithin W.flow hM04 T x (uniqueDiffOn_Icc hac) htime hs hy)
  simp only [smul_apply, smul_eq_mul, M08.chartRicciForm_at hM04 _ (gauge_chart_source b x y)] at h
  rw [ht, (ordinaryGauge_movingCalculus b hCoordinates W).ricci_eq] at h
  simpa only [openSubset_chartFrame, gauge_extChartAt_eq_val, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h

end PoincareConjecture.M14
