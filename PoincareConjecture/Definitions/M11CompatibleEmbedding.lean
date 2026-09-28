import PoincareConjecture.Definitions.M11SpacetimeSlices
import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval}

structure SpacetimeWorldline (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) where
  interval_subset : K.domain ⊆ I.domain
  curve : D.Point → F.Point
  smooth : ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞ curve
  time_eq : ∀ t, F.timeFunction (curve t) = t.val
  derivative_eq : ∀ t,
    mfderiv (𝓡∂ 1) (spacetimeModel n) curve t (D.positiveTangent t) =
      F.timeVector (curve t)

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

structure CompatibleSpacetimeCylinder (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    extends CompatibleSpacetimeEmbedding F D C where
  smooth : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ toSpacetime
  differential_injective : ∀ p,
    Function.Injective (mfderiv (spacetimeModel n) (spacetimeModel n) toSpacetime p)

def CompatibleSpacetimeEmbedding.IsBasedAt
    {F : GeneralizedFlowSpacetime n X time I} {D : SmoothSpacetimeInterval K}
    {C : Type v} [TopologicalSpace C] (e : CompatibleSpacetimeEmbedding F D C)
    (t : D.Point) (source : C → F.Point) : Prop :=
  ∀ x, e.toSpacetime (t, x) = source x

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

end PoincareConjecture
