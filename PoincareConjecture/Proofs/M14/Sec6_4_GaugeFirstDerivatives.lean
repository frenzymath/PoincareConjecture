import PoincareConjecture.Proofs.M14.Sec6_4_GaugeCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.RicciDerivative










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem horizontalRicciDerivativePairing_symm (q : G.Point) (U V W : G.Horizontal q) :
    M14HorizontalRicciDerivativePairing G q U V W =
      M14HorizontalRicciDerivativePairing G q U W V := by
  let D := G.leafwise.sliceConnection (G.spacetime.timeFunction q)
  exact D.covariantTensorDerivative_ricciEvaluation_symm
    D.normalization_curvatureTensorCalculus _ _ _ _



theorem movingGauge_scalarDifferential
    {K : SpacetimeInterval} {T : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    {e : MovingSpacetimeGauge G.spacetime T C} {g : MovingSpacetimeGaugeGeometry e}
    {c : MetricLeviCivitaFamily g.metric} (H : MovingGaugeCalculus G.leafwise g c)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (t : T.Point) (x : C) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (c t.val).scalarCurvature x v =
      M14HorizontalScalarDifferential G (e.toSpacetime (t, x))
        (g.spatialTangentEquiv t x v).val := by
  have he : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : C => e.toSpacetime (t, y)) :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have heq : (c t.val).scalarCurvature =
      horizontalScalarCurvature G.leafwise ∘ (fun y : C => e.toSpacetime (t, y)) :=
    funext (H.scalar_eq t)
  rw [heq, mvfderiv_comp_apply x (hscalar.mdifferentiable (by simp) _)
    (he.mdifferentiable (by simp) _), ← g.spatialTangentEquiv_eq]
  rfl



theorem gauge_chartActionPotential_differential (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (hM04 : RicciFlowCurvatureTheory.{0}) (T : ℝ) {C : Set ℝ}
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain)
    (x y : G.gaugeCover.spatial b) {s : ℝ} (hs : s ∈ C)
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (ht : T - s ^ 2 = t.val) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => M08.chartActionPotential W.flow T x (s, z)) y.val v =
      2 * s ^ 2 * M14HorizontalScalarDifferential G
        ((G.gaugeCover.cylinder b).toSpacetime (t, y))
        ((G.gaugeCover.metric b).spatialTangentEquiv t y v).val := by
  have hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rw [(G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ y
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by
    simpa only [extChartAt_source] using hy
  have hval : extChartAt (𝓡 n) x y = y.val := by
    rw [extChartAt_coe]
    rfl
  have hd := M08.hasFDerivAt_spatialWithin (isOpen_extChartAt_target (I := 𝓡 n) x) _
    (M08.chartActionPotential_closed_contDiffOn W.flow hM04 T x htime) hs
    ((extChartAt (𝓡 n) x).map_source hy')
  have h := M08.chartActionPotential_closed_spatial_apply W.flow hM04 T htime hy hs v
  rw [← hd.fderiv, ht, movingGauge_scalarDifferential
    (ordinaryGauge_movingCalculus b hCoordinates W) hscalar] at h
  simpa only [hval, openSubset_chartFrame, ordinaryGaugeGeometry,
    CompatibleSpacetimeCylinder.toMovingSpacetimeGauge] using h

end PoincareConjecture.M14
