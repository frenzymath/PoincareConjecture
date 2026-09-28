import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.CurvatureTransport
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Differential
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.EquationBridge
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.MetricDerivative











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

theorem movingGaugeCalculus_of_derivatives
    (D : LeafwiseLeviCivitaFamily F S) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    (hDrift : ContMDiff (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : T.Point × C => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 (movingGaugeDrift G p.1 p.2)))
    (hMetricDerivative : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (G.metric s).inner x u v)
        (horizontalMetricLieDerivative F (e.toSpacetime (t, x))
          (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v) -
            ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
              (movingGaugeDrift G t) x u v) K.domain t.val)
    (hLeaf : ∀ (V : HorizontalSection F) (O : Set F.Point),
      IsOpen O → IsSmoothHorizontalSectionOn F V O →
      ∀ (t : T.Point) (x : C), e.toSpacetime (t, x) ∈ O →
      ∀ u : TangentSpace (𝓡 n) x,
        rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x))
          (G.spatialTangentEquiv t x u) =
        G.spatialTangentEquiv t x ((c t.val).connection (pullbackHorizontalSection G V t) x u))
    (hHorizontal : ∀ (V : HorizontalSection F) (O : Set F.Point),
      IsOpen O → IsSmoothHorizontalSectionOn F V O →
      ∀ (t : T.Point) (x : C), e.toSpacetime (t, x) ∈ O →
      ∀ (a : ℝ) (u : TangentSpace (𝓡 n) x),
        rawHorizontalCovariantDerivative D V (e.toSpacetime (t, x))
          (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
            (a • T.positiveTangent t, u)) =
        G.spatialTangentEquiv t x
          (a • movingGaugeSectionTimeDerivative G V t x +
            (c t.val).connection (pullbackHorizontalSection G V t) x u -
              a • (c t.val).connection (movingGaugeDrift G t) x
                (pullbackHorizontalSection G V t x))) : MovingGaugeCalculus D G c := by
  have hs := movingGaugeSliceGeometryFields (S := S) e G
  have hc := movingGaugeCurvatureTransportFields D e G c
  exact
    { slice_localDiffeomorph := hs.slice_localDiffeomorph
      slice_tangent_eq := hs.slice_tangent_eq
      slice_metric_eq := hs.slice_metric_eq
      drift_smooth := hDrift
      time_vector_eq := movingGauge_time_vector_eq e G
      projection_eq := movingGauge_projection_eq e G
      metric_derivative := hMetricDerivative
      riemann_eq := hc.riemann_eq
      ricci_eq := hc.ricci_eq
      scalar_eq := hc.scalar_eq
      curvature_norm_eq := hc.curvature_norm_eq
      leafwise_derivative_eq := hLeaf
      horizontal_derivative_eq := hHorizontal
      equation_iff := movingGaugeEquation_iff_of_metric_derivative_ricci_eq D G c
        hMetricDerivative hc.ricci_eq }


theorem movingGaugeCalculus
    (D : LeafwiseLeviCivitaFamily F S) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric) : MovingGaugeCalculus D G c := by
  have hSection := movingGaugeSectionTransportFields D e G c
  exact movingGaugeCalculus_of_derivatives D G c hSection.drift_smooth
    (movingGauge_metric_derivative D G c) hSection.leafwise_derivative_eq
    hSection.horizontal_derivative_eq

end PoincareConjecture
