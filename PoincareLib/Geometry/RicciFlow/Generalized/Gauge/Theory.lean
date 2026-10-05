import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Calculus

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M12GaugeTheory.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Ricci equations on actual spacetime gauges

Morgan-Tian Definitions 3.36-3.38 and Remark 3.37, pp. 60-61, with the
moving-pullback convention MT-DETURCK-PULLBACK-SIGN. Each equivalence uses
the actual image of its supplied gauge. A global converse requires the
displayed covering family. These are M12 conclusions over its supplied
adapted cover; no ordinary Ricci flow is assumed in the geometric inputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

/-- Gauge geometry, actual Ricci-flow witnesses, and equation transport for
the same spacetime, selected slice connections, and interval system. -/
structure SpacetimeGaugeTheory (D : LeafwiseLeviCivitaFamily F S)
    (T : SpacetimeIntervalSystem) : Prop where
  moving_geometry : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : MovingSpacetimeGauge F (T.interval K) C),
    Nonempty (MovingSpacetimeGaugeGeometry e)
  moving_connections : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : MovingSpacetimeGauge F (T.interval K) C)
    (G : MovingSpacetimeGaugeGeometry e),
    Nonempty (MetricLeviCivitaFamily G.metric)
  moving_calculus : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : MovingSpacetimeGauge F (T.interval K) C)
    (G : MovingSpacetimeGaugeGeometry e) (c : MetricLeviCivitaFamily G.metric),
    MovingGaugeCalculus D G c
  compatible_zero_drift : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (T.interval K) C)
    (G : SpacetimeCylinderMetric e), ∀ (t : (T.interval K).Point) (x : C),
      movingGaugeDrift G.toMovingSpacetimeGaugeGeometry t x = 0
  compatible_equivalence : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (T.interval K) C)
    (G : SpacetimeCylinderMetric e) (c : MetricLeviCivitaFamily G.metric),
    IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) ↔
      OrdinaryMetricRicciPDE G.metric c K
  compatible_ordinary : ∀ (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (T.interval K) C)
    (G : SpacetimeCylinderMetric e),
    IntrinsicGeneralizedRicciEquationOn D (Set.range e.toSpacetime) →
      Nonempty (OrdinaryGaugeWitness D e G)
  compatible_realization : IntrinsicGeneralizedRicciEquation D →
    ∀ (C : Type v) [TopologicalSpace C]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
      (K : SpacetimeInterval) (e : CompatibleSpacetimeCylinder F (T.interval K) C),
      ∃ G : SpacetimeCylinderMetric e, Nonempty (OrdinaryGaugeWitness D e G)
  cover_converse : ∀ (B : Type u) (C : B → Type v)
    [∀ b, TopologicalSpace (C b)]
    [∀ b, ChartedSpace (EuclideanSpace ℝ (Fin n)) (C b)]
    [∀ b, IsManifold (𝓡 n) ∞ (C b)]
    (K : B → SpacetimeInterval)
    (e : ∀ b, CompatibleSpacetimeCylinder F (T.interval (K b)) (C b))
    (G : ∀ b, SpacetimeCylinderMetric (e b))
    (c : ∀ b, MetricLeviCivitaFamily (G b).metric),
    (∀ p : F.Point, ∃ b, ∃ q : (T.interval (K b)).Point × C b,
      (e b).toSpacetime q = p) →
    (∀ b, OrdinaryMetricRicciPDE (G b).metric (c b) (K b)) →
      IntrinsicGeneralizedRicciEquation D

end PoincareMT
