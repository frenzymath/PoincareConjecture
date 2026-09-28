import PoincareConjecture.Definitions.M12GaugeTransport
import PoincareConjecture.Definitions.M12GeneralizedEquation











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



structure MovingGaugeCalculus (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e) (c : MetricLeviCivitaFamily G.metric) : Prop where
  slice_localDiffeomorph : ∀ t : T.Point,
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (movingGaugeSliceMap e S t)
  slice_tangent_eq : ∀ (t : T.Point) (x : C) (u : TangentSpace (𝓡 n) x),
    (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) =
        G.spatialTangentEquiv t x u
  slice_metric_eq : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
    (S t.val).metricOnPoints.inner (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x v) =
        (G.metric t.val).inner x u v
  drift_smooth : ContMDiff (spacetimeModel n)
    ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
    (fun p : T.Point × C ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := (TangentSpace (𝓡 n) : C → Type _)) p.2 (movingGaugeDrift G p.1 p.2))
  time_vector_eq : ∀ (t : T.Point) (x : C),
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
      (T.positiveTangent t, movingGaugeDrift G t x) =
        F.timeVector (e.toSpacetime (t, x))
  projection_eq : ∀ (t : T.Point) (x : C) (a : ℝ) (u : TangentSpace (𝓡 n) x),
    F.horizontalProjection (e.toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (a • T.positiveTangent t, u)) =
      G.spatialTangentEquiv t x (u - a • movingGaugeDrift G t x)
  metric_derivative : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
    HasDerivWithinAt (fun s ↦ (G.metric s).inner x u v)
      (horizontalMetricLieDerivative F (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v) -
          ordinaryMetricLieDerivative (G.metric t.val) (c t.val)
            (movingGaugeDrift G t) x u v) K.domain t.val
  riemann_eq : ∀ (t : T.Point) (x : C) (u v w z : TangentSpace (𝓡 n) x),
    (c t.val).curvatureTensor x u v w z =
      horizontalRiemann D (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)
        (G.spatialTangentEquiv t x w) (G.spatialTangentEquiv t x z)
  ricci_eq : ∀ (t : T.Point) (x : C) (u v : TangentSpace (𝓡 n) x),
    (c t.val).ricci x u v = horizontalRicci D (e.toSpacetime (t, x))
      (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)
  scalar_eq : ∀ (t : T.Point) (x : C),
    (c t.val).scalarCurvature x = horizontalScalarCurvature D (e.toSpacetime (t, x))
  curvature_norm_eq : ∀ (t : T.Point) (x : C),
    (c t.val).curvatureTensorNorm x = horizontalCurvatureNorm D (e.toSpacetime (t, x))
  leafwise_derivative_eq : ∀ (V : HorizontalSection F) (O : Set F.Point),
    IsOpen O → IsSmoothHorizontalSectionOn F V O →
    ∀ (t : T.Point) (x : C), e.toSpacetime (t, x) ∈ O →
    ∀ u : TangentSpace (𝓡 n) x,
      rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) =
      G.spatialTangentEquiv t x ((c t.val).connection (pullbackHorizontalSection G V t) x u)
  horizontal_derivative_eq : ∀ (V : HorizontalSection F) (O : Set F.Point),
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
              (pullbackHorizontalSection G V t x))
  equation_iff : IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) ↔
    MovingGaugeRicciPDE G c

end PoincareConjecture
