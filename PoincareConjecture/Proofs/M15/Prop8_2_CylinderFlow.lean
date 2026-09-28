import PoincareConjecture.Definitions.M15Noncollapsing
import PoincareConjecture.Statements.M12GeneralizedEquation










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]




theorem actualBallCylinder_exists_flow
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C) :
    ∃ F : RicciFlow n C K.domain, F.metric = B.metric.metric ∧
      (∀ (t : (G.timeIntervals.interval K).Point) (c : C),
        (F.connection t.val).curvatureTensorNorm c =
          horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (t, c))) ∧
      (∀ (t : (G.timeIntervals.interval K).Point) (c : C),
        (F.connection t.val).scalarCurvature c =
          horizontalScalarCurvature G.leafwise (B.embedding.toSpacetime (t, c))) := by
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals
    G.gaugeCover G.leafwise
  obtain ⟨c⟩ := H.moving_connections C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry
  have heq : IntrinsicGeneralizedRicciEquationOn G.leafwise
      (Set.range B.embedding.toSpacetime) := fun p _ u v => G.ricciEquation p u v
  have hPDE := (H.compatible_equivalence C K B.embedding B.metric c).mp heq
  let F : RicciFlow n C K.domain :=
    { metric := B.metric.metric
      connection := c
      interval := K.ordConnected
      nontrivial := K.nontrivial
      smooth := B.metric.smooth
      equation := hPDE }
  have hcalc := H.moving_calculus C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry c
  exact ⟨F, rfl, hcalc.curvature_norm_eq, hcalc.scalar_eq⟩




theorem actualBallCylinder_terminal_sliceMap_eq
    (B : M15ActualBallCylinder G T x r K C) :
    movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices
      ⟨T, B.base_mem⟩ = B.source_map := by
  funext c
  exact Subtype.ext (B.based c)




theorem actualBallCylinder_terminal_metric_pullback
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (c : C) (u v : TangentSpace (𝓡 n) c) :
    (G.slices T).metricOnPoints.inner (B.source_map c)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map c u)
      (mfderiv (𝓡 n) (𝓡 n) B.source_map c v) =
        (B.metric.metric T).inner c u v := by
  have H := hM12.gauges X time I G.spacetime G.slices G.timeIntervals
    G.gaugeCover G.leafwise
  obtain ⟨D⟩ := H.moving_connections C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry
  have hcalc := H.moving_calculus C K B.embedding.toMovingSpacetimeGauge
    B.metric.toMovingSpacetimeGaugeGeometry D
  have h := hcalc.slice_metric_eq ⟨T, B.base_mem⟩ c u v
  rw [actualBallCylinder_terminal_sliceMap_eq B] at h
  exact h

end PoincareConjecture.Proofs.M15
