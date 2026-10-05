import PoincareLib.Geometry.Spacetime.Horizontal.Basic
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Moving
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Cover

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M12GeneralizedEquation.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Intrinsic and ordinary Ricci equations

Morgan-Tian Definitions 3.1-3.2 and 3.36-3.38, pp. 35 and 60-61.
The ordinary PDE is imposed on a supplied metric and connection family,
before an ordinary flow witness is constructed. Every moving drift is
determined by its actual gauge map. All included times use within derivatives.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

section Ordinary

variable {n : ℕ} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

/-- A retained connection for every member of one total metric family. -/
abbrev MetricLeviCivitaFamily (g : ℝ → RiemannianMetric n C) :=
  (t : ℝ) → LeviCivitaData (g t)

/-- The actual ordinary equation, without assuming an existing RicciFlow. -/
def OrdinaryMetricRicciPDE (g : ℝ → RiemannianMetric n C)
    (D : MetricLeviCivitaFamily g) (I : SpacetimeInterval) : Prop :=
  ∀ t ∈ I.domain, ∀ x : C, ∀ u v : TangentSpace (𝓡 n) x,
    HasDerivWithinAt (fun s ↦ (g s).inner x u v)
      (-2 * (D t).ricci x u v) I.domain t

/-- The spatial metric Lie expression through its actual compatible connection. -/
noncomputable def ordinaryMetricLieDerivative (g : RiemannianMetric n C)
    (D : LeviCivitaData g) (V : (x : C) → TangentSpace (𝓡 n) x)
    (x : C) (u v : TangentSpace (𝓡 n) x) : ℝ :=
  g.inner x (D.connection V x u) v + g.inner x u (D.connection V x v)

end Ordinary

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

/-- The intrinsic equation restricted to an actual subset of spacetime. -/
def IntrinsicGeneralizedRicciEquationOn (D : LeafwiseLeviCivitaFamily F S)
    (U : Set F.Point) : Prop :=
  ∀ p ∈ U, ∀ u v : F.Horizontal p,
    horizontalMetricLieDerivative F p u v = -2 * horizontalRicci D p u v

/-- Generalized Ricci-flow data retain actual slice connections and the intrinsic PDE. -/
structure IntrinsicRicciFlow (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) where
  leafwiseConnection : LeafwiseLeviCivitaFamily F S
  equation : IntrinsicGeneralizedRicciEquation leafwiseConnection

variable {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

/-- The moving-gauge equation with the actual drift and the corrected minus sign. -/
def MovingGaugeRicciPDE {e : MovingSpacetimeGauge F T C}
    (G : MovingSpacetimeGaugeGeometry e) (D : MetricLeviCivitaFamily G.metric) : Prop :=
  ∀ t (ht : t ∈ K.domain), ∀ x : C, ∀ u v : TangentSpace (𝓡 n) x,
    HasDerivWithinAt (fun s ↦ (G.metric s).inner x u v)
      (-2 * (D t).ricci x u v - ordinaryMetricLieDerivative (G.metric t) (D t)
        (movingGaugeDrift G ⟨t, ht⟩) x u v) K.domain t

/-- An actual ordinary flow on the supplied compatible cylinder, with the
same metric representative and actual horizontal metric/Ricci pullbacks. -/
structure OrdinaryGaugeWitness (D : LeafwiseLeviCivitaFamily F S)
    (e : CompatibleSpacetimeCylinder F T C) (G : SpacetimeCylinderMetric e) where
  flow : RicciFlow n C K.domain
  metric_eq : flow.metric = G.metric
  metric_pullback : ∀ t : T.Point, ∀ x u v,
    (flow.metric t.val).inner x u v =
      F.horizontalMetric.inner (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)
  ricci_pullback : ∀ t : T.Point, ∀ x u v,
    (flow.connection t.val).ricci x u v =
      horizontalRicci D (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)

end PoincareMT
