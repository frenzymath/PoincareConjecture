import PoincareLib.Geometry.Spacetime.Cylinder.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M12MovingGauge.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Moving gauges in an actual spacetime

A moving gauge preserves time but need not follow the selected time vector.
Its drift is determined by its actual differential. The pullback metric and
spatial tangent equivalence are construction outputs of M12. Compatible
cylinders from Morgan-Tian Definition 3.38, p. 61, supply special cases.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval}

/-- A jointly smooth time-preserving gauge with an injective actual
differential. Following the spacetime's time vector is not assumed. -/
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

/-- A compatible cylinder regarded as a moving gauge on the same domain. -/
def CompatibleSpacetimeCylinder.toMovingSpacetimeGauge
    (e : CompatibleSpacetimeCylinder F D C) : MovingSpacetimeGauge F D C where
  interval_subset := e.interval_subset
  toSpacetime := e.toSpacetime
  embedding := e.embedding
  time_eq := e.time_eq
  smooth := e.smooth
  differential_injective := e.differential_injective

/-- The metric and spatial tangent identification induced by the actual
gauge. Only metric values on its stated interval are constrained. -/
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

/-- Existing cylinder metric data yield geometry for its identical moving
gauge without choosing another metric or differential. -/
def SpacetimeCylinderMetric.toMovingSpacetimeGaugeGeometry
    {e : CompatibleSpacetimeCylinder F D C} (G : SpacetimeCylinderMetric e) :
    MovingSpacetimeGaugeGeometry e.toMovingSpacetimeGauge where
  metric := G.metric
  smooth := G.smooth
  spatialTangentEquiv := G.spatialTangentEquiv
  spatialTangentEquiv_eq := G.spatialTangentEquiv_eq
  metric_eq := G.metric_eq

/-- The actual velocity of the gauge in the positive interval-time direction. -/
noncomputable def movingGaugeTimeVelocity (e : MovingSpacetimeGauge F D C)
    (t : D.Point) (x : C) :
    TangentSpace (spacetimeModel n) (e.toSpacetime (t, x)) :=
  mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
    (D.positiveTangent t, 0)

/-- The uniquely determined spatial drift: the inverse spatial differential
of the negative horizontal component of the gauge's actual time velocity. -/
noncomputable def movingGaugeDrift {e : MovingSpacetimeGauge F D C}
    (G : MovingSpacetimeGaugeGeometry e) (t : D.Point) (x : C) :
    TangentSpace (𝓡 n) x :=
  (G.spatialTangentEquiv t x).symm
    (-F.horizontalProjection (e.toSpacetime (t, x)) (movingGaugeTimeVelocity e t x))

/-- The actual spatial gauge map into the selected geometry on its time slice. -/
def movingGaugeSliceMap (e : MovingSpacetimeGauge F D C)
    (S : ∀ s : ℝ, SpacetimeSliceGeometry F s) (t : D.Point) : C → (S t.val).Point :=
  fun x ↦ ⟨e.toSpacetime (t, x), e.time_eq (t, x)⟩

end PoincareMT
