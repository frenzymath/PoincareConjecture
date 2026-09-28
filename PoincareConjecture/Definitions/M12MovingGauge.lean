import PoincareConjecture.Definitions.M11CompatibleEmbedding

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval}

structure MovingSpacetimeGauge (F : GeneralizedFlowSpacetime n X time I)
    (D : SmoothSpacetimeInterval K) (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C] where
  interval_subset : K.domain ⊆ I.domain
  toSpacetime : D.Point × C → F.Point
  embedding : Topology.IsEmbedding toSpacetime
  time_eq : ∀ p, F.timeFunction (toSpacetime p) = p.1.val
  smooth : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ toSpacetime
  differential_injective : ∀ p,
    Function.Injective (mfderiv (spacetimeModel n) (spacetimeModel n) toSpacetime p)

variable {F : GeneralizedFlowSpacetime n X time I} {D : SmoothSpacetimeInterval K}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

def CompatibleSpacetimeCylinder.toMovingSpacetimeGauge
    (e : CompatibleSpacetimeCylinder F D C) : MovingSpacetimeGauge F D C where
  interval_subset := e.interval_subset
  toSpacetime := e.toSpacetime
  embedding := e.embedding
  time_eq := e.time_eq
  smooth := e.smooth
  differential_injective := e.differential_injective

structure MovingSpacetimeGaugeGeometry (e : MovingSpacetimeGauge F D C) where
  metric : ℝ → RiemannianMetric n C
  smooth : RiemannianMetric.IsSmoothFamilyOn metric K.domain
  spatialTangentEquiv : ∀ t : D.Point, ∀ x : C,
    TangentSpace (𝓡 n) x ≃L[ℝ] F.Horizontal (e.toSpacetime (t, x))
  spatialTangentEquiv_eq : ∀ t x v, (spatialTangentEquiv t x v).val =
    mfderiv (𝓡 n) (spacetimeModel n) (fun y : C ↦ e.toSpacetime (t, y)) x v
  metric_eq : ∀ t : D.Point, ∀ x v w, (metric t.val).inner x v w =
    F.horizontalMetric.inner (e.toSpacetime (t, x))
      (spatialTangentEquiv t x v) (spatialTangentEquiv t x w)

def SpacetimeCylinderMetric.toMovingSpacetimeGaugeGeometry
    {e : CompatibleSpacetimeCylinder F D C} (G : SpacetimeCylinderMetric e) :
    MovingSpacetimeGaugeGeometry e.toMovingSpacetimeGauge where
  metric := G.metric
  smooth := G.smooth
  spatialTangentEquiv := G.spatialTangentEquiv
  spatialTangentEquiv_eq := G.spatialTangentEquiv_eq
  metric_eq := G.metric_eq

noncomputable def movingGaugeTimeVelocity (e : MovingSpacetimeGauge F D C)
    (t : D.Point) (x : C) :
    TangentSpace (spacetimeModel n) (e.toSpacetime (t, x)) :=
  mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
    (D.positiveTangent t, 0)

noncomputable def movingGaugeDrift {e : MovingSpacetimeGauge F D C}
    (G : MovingSpacetimeGaugeGeometry e) (t : D.Point) (x : C) :
    TangentSpace (𝓡 n) x :=
  (G.spatialTangentEquiv t x).symm
    (-F.horizontalProjection (e.toSpacetime (t, x)) (movingGaugeTimeVelocity e t x))

def movingGaugeSliceMap (e : MovingSpacetimeGauge F D C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s) (t : D.Point) : C → (S t.val).Point :=
  fun x ↦ ⟨e.toSpacetime (t, x), e.time_eq (t, x)⟩

end PoincareConjecture
