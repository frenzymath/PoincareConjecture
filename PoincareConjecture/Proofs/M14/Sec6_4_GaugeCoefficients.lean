import PoincareConjecture.Proofs.M14.Sec6_4_OrdinaryGauge
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeTensorDerivatives
import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetConnection
import PoincareConjecture.Proofs.M08.SecondVariationCoefficients










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14



theorem openSubset_chartFrame {n : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (x y : U) (v : EuclideanSpace ℝ (Fin n)) : M08.chartFrame x v y = v :=
  U.tangent_trivialization_symmL_apply x y v

private theorem openSubset_extChartAt {n : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) (x y : U) :
    extChartAt (𝓡 n) x y = y.val := by
  rw [extChartAt_coe]
  rfl




theorem openSubset_chartConnection {n : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    {J C : Set ℝ} (F : RicciFlow n U J) (T : ℝ)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) (x y : U) {s : ℝ} (hs : s ∈ C)
    (v w : EuclideanSpace ℝ (Fin n)) :
    (F.connection (T - s ^ 2)).connection (fun _ : U => w) y v =
      M08.closedChartConnection F T x C (s, y.val) v w := by
  have hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rw [U.chartAt_source_eq_univ]
    exact mem_univ y
  have hframe : M08.chartFrame x w = fun _ : U => w :=
    funext (fun y => openSubset_chartFrame U x y w)
  have h := M08.closedChartChristoffel_connection F T htime hy hs v w
  rw [hframe] at h
  simpa only [openSubset_chartFrame, openSubset_extChartAt,
    M08.closedChartConnection_apply] using h

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))

private theorem gauge_chart_source (x y : G.gaugeCover.spatial b) :
    y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
  rw [(G.gaugeCover.spatial b).chartAt_source_eq_univ]
  exact mem_univ y



theorem gauge_chartActionMetric (T : ℝ) (x y : G.gaugeCover.spatial b) (s : ℝ)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v w : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric W.flow T x (s, y.val) v w =
      G.spacetime.horizontalMetric.inner ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have h := M08.chartActionMetric_apply W.flow T (gauge_chart_source b x y) s v w
  rw [openSubset_chartFrame, openSubset_chartFrame, ht, W.metric_pullback] at h
  exact h



theorem gauge_chartActionPotential
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (T : ℝ) (x y : G.gaugeCover.spatial b) (s : ℝ)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) :
    M08.chartActionPotential W.flow T x (s, y.val) =
      2 * s ^ 2 * horizontalScalarCurvature G.leafwise
        ((G.gaugeCover.cylinder b).toSpacetime (t, y)) := by
  have h := M08.chartActionPotential_apply W.flow T (gauge_chart_source b x y) s
  rw [ht, (ordinaryGauge_movingCalculus b hCoordinates W).scalar_eq] at h
  exact h



theorem gauge_coordinateCurvature_pair
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v a w z : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric W.flow T x (s, y.val)
        (M08.coordinateCurvature (M08.closedChartConnection W.flow T x C)
          (s, y.val) v a w) z =
      horizontalRiemann G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y a)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y z)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have h := M08.coordinateCurvature_pair W.flow hM04 T hC htime
    (gauge_chart_source b x y) hs hsN v a w z
  rw [ht, (ordinaryGauge_movingCalculus b hCoordinates W).riemann_eq] at h
  simpa only [openSubset_chartFrame, openSubset_extChartAt, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h



theorem gauge_chartActionPotential_hessian
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun q => M08.chartActionPotential W.flow T x (s, q))) y.val v w -
      fderiv ℝ (fun q => M08.chartActionPotential W.flow T x (s, q)) y.val
        (M08.closedChartConnection W.flow T x C (s, y.val) v w) =
      2 * s ^ 2 * M14HorizontalHessianPairing G
        ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have h := M08.chartActionPotential_hessian W.flow hM04 T hC htime
    (gauge_chart_source b x y) hs v w
  rw [ht, movingGauge_horizontalHessianPairing
    (ordinaryGauge_movingCalculus b hCoordinates W) hscalar] at h
  simpa only [openSubset_chartFrame, openSubset_extChartAt, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h




theorem gauge_chartConnection_time_pair
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v w z : EuclideanSpace ℝ (Fin n)) :
    M08.chartActionMetric W.flow T x (s, y.val)
        (fderiv ℝ (M08.closedChartConnection W.flow T x C) (s, y.val) (1, 0) v w) z =
      2 * s * M14BcalPairing G ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y z) := by
  have h := M08.closedChartConnection_time_pair_interior W.flow hM04 T hC htime
    (gauge_chart_source b x y) hs hsN v w z
  rw [ht, movingGauge_bcalPairing (ordinaryGauge_movingCalculus b hCoordinates W)] at h
  simpa only [openSubset_chartFrame, openSubset_extChartAt, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h




theorem gauge_chartActionMetric_time_pair
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
    (hC : UniqueDiffOn ℝ C) (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C) (hsN : C ∈ 𝓝 s)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (M08.chartActionMetric W.flow T x) (s, y.val) (1, 0) v w =
      4 * s * horizontalRicci G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v)
        ((G.gaugeCover.metric b).spatialTangentEquiv t y w) := by
  have h := M08.chartActionMetric_time_pair_interior W.flow hM04 T hC htime
    (gauge_chart_source b x y) hs hsN v w
  rw [ht, (ordinaryGauge_movingCalculus b hCoordinates W).ricci_eq] at h
  simpa only [openSubset_chartFrame, openSubset_extChartAt, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h

end PoincareConjecture.M14
