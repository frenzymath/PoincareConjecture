import PoincareLib.Geometry.Spacetime.Slice
import PoincareLib.Geometry.RicciFlow.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M11CompatibleEmbedding.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Compatible worldlines and cylinders

Morgan-Tian Definition 3.38, p. 61. All derivatives are derivatives of the
actual maps into the selected spacetime. Topological sources need no manifold
structure. Smooth cylinders additionally have an injective differential;
smooth topological embeddings alone do not guarantee positive pullback metrics.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval}

/-- An actual integral curve parameterized by the specified time interval. -/
structure SpacetimeWorldline (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) where
  interval_subset : K.domain ⊆ I.domain
  curve : D.Point → F.Point
  smooth : ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞ curve
  time_eq : ∀ t, F.timeFunction (curve t) = t.val
  derivative_eq : ∀ t,
    mfderiv (𝓡∂ 1) (spacetimeModel n) curve t (D.positiveTangent t) =
      F.timeVector (curve t)

/-- Compatibility for an arbitrary topological source, including a closed
subset of a slice. Spatial manifold differentiation is not assumed. -/
structure CompatibleSpacetimeEmbedding (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) (C : Type v) [TopologicalSpace C] where
  interval_subset : K.domain ⊆ I.domain
  toSpacetime : D.Point × C → F.Point
  embedding : Topology.IsEmbedding toSpacetime
  time_eq : ∀ p, F.timeFunction (toSpacetime p) = p.1.val
  worldline_smooth : ∀ x, ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞
    (fun t : D.Point ↦ toSpacetime (t, x))
  worldline_derivative : ∀ t x,
    mfderiv (𝓡∂ 1) (spacetimeModel n) (fun s : D.Point ↦ toSpacetime (s, x)) t
      (D.positiveTangent t) = F.timeVector (toSpacetime (t, x))

/-- Compatibility on a smooth spatial source, with joint smoothness and
full-rank actual differential, including the source's time endpoints. -/
structure CompatibleSpacetimeCylinder (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    extends CompatibleSpacetimeEmbedding F D C where
  smooth : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ toSpacetime
  differential_injective : ∀ p,
    Function.Injective (mfderiv (spacetimeModel n) (spacetimeModel n) toSpacetime p)

/-- The specified source map is the actual map at the included base time. -/
def CompatibleSpacetimeEmbedding.IsBasedAt
    {F : GeneralizedFlowSpacetime n X time I} {D : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C] (e : CompatibleSpacetimeEmbedding F D C)
    (t : D.Point) (source : C → F.Point) : Prop :=
  ∀ x, e.toSpacetime (t, x) = source x

/-- The jointly smooth metric pulled back by the actual compatible cylinder.
Only values on the specified interval are compared with the spacetime metric. -/
structure SpacetimeCylinderMetric {F : GeneralizedFlowSpacetime n X time I}
    {D : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder F D C) where
  metric : ℝ → RiemannianMetric n C
  smooth : RiemannianMetric.IsSmoothFamilyOn metric K.domain
  spatialTangentEquiv : ∀ t : D.Point, ∀ x : C,
    TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal (e.toSpacetime (t, x))
  spatialTangentEquiv_eq : ∀ t x v, (spatialTangentEquiv t x v).val =
    mfderiv (𝓡 n) (spacetimeModel n) (fun y : C ↦ e.toSpacetime (t, y)) x v
  metric_eq : ∀ t : D.Point, ∀ x v w, (metric t.val).inner x v w =
    F.horizontalMetric.inner (e.toSpacetime (t, x))
      (spatialTangentEquiv t x v) (spatialTangentEquiv t x w)

end PoincareMT
