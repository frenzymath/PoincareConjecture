import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Calculus
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.SliceMap

/-!
# Slice geometry fields of a moving gauge

The three slice fields in `MovingGaugeCalculus` are consequences of the
dependent slice-map construction.  They are kept together here so the
calculus assembly can consume one checked geometric package.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ s : ℝ, SpacetimeSliceGeometry F s}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

/-- The three exact geometric fields contributed by the moving slice map. -/
structure MovingGaugeSliceGeometryFields
    (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e) : Prop where
  slice_localDiffeomorph : ∀ t : T.Point,
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (movingGaugeSliceMap e S t)
  slice_tangent_eq : ∀ (t : T.Point) (x : C) (u : TangentSpace (𝓡 n) x),
    (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u) =
        G.spatialTangentEquiv t x u
  slice_metric_eq : ∀ (t : T.Point) (x : C)
      (u v : TangentSpace (𝓡 n) x),
    (S t.val).metricOnPoints.inner (movingGaugeSliceMap e S t x)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u)
      (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x v) =
        (G.metric t.val).inner x u v

/-- Construct the slice-geometry fields from the checked `SliceMap` laws. -/
theorem movingGaugeSliceGeometryFields
    (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e) :
    MovingGaugeSliceGeometryFields (S := S) e G where
  slice_localDiffeomorph := fun t ↦ movingGaugeSliceMap_localDiffeomorph e S G t
  slice_tangent_eq := fun t x u ↦ movingGaugeSliceMap_tangent_eq e S G t x u
  slice_metric_eq := fun t x u v ↦
    movingGaugeSliceMap_metric_eq e S G t x u v
      (movingGaugeSliceMap_tangent_eq e S G t x u)
      (movingGaugeSliceMap_tangent_eq e S G t x v)

end PoincareMT
