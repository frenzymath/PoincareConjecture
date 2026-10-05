import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.MetricPredecessors
import PoincareLib.Geometry.Spacetime.Horizontal.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Theory

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M12GeneralizedEquation.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# M12 intrinsic Ricci equation and actual gauge realization

Morgan-Tian Definition 3.36 and Remark 3.37, pp. 60-61. The input cover is
the concrete covering supplied by the M11 atlas realization. All operators,
slice choices, cylinders and pullback metrics refer to the same spacetime.
The ordinary-product clause constructs that cover on the given metric family.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- Actual product geometry and its intrinsic equation for the given metric family.
The retained M11 product identifies both the carrier and the full metric representative. -/
structure OrdinaryProductRicciGeometry {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval) where
  product : OrdinaryProductSpacetimeConclusion g I
  cover : SpacetimeGaugeCover product.spacetime product.timeIntervals
  leafwiseConnection : LeafwiseLeviCivitaFamily product.spacetime product.slices
  equation_iff : ∀ c : MetricLeviCivitaFamily g,
    IntrinsicGeneralizedRicciEquation leafwiseConnection ↔ OrdinaryMetricRicciPDE g c I
  ordinary_from_equation : IntrinsicGeneralizedRicciEquation leafwiseConnection →
    Nonempty (OrdinaryGaugeWitness leafwiseConnection product.productCylinder product.productMetric)

/-- M12's complete construction and equivalence problem in arbitrary dimension.
The supplied adapted cover is geometric data; it assumes no Ricci equation,
curvature identity, connection naturality or analytic estimate. -/
structure GeneralizedRicciGaugeTheory (n : ℕ) : Prop where
  leafwise_calculus : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
    (_cover : SpacetimeGaugeCover F T),
    Nonempty (LeafwiseLeviCivitaFamily F S) ∧
      ∀ D : LeafwiseLeviCivitaFamily F S, HorizontalRicciCalculus D
  gauges : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
    (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
    SpacetimeGaugeTheory.{u, u} D T
  coordinate_gauges : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
    (_cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
    SpacetimeGaugeTheory.{u, 0} D T
  adapted_equation : ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
    (I : SpacetimeInterval) (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) (T : SpacetimeIntervalSystem)
    (cover : SpacetimeGaugeCover F T) (D : LeafwiseLeviCivitaFamily F S),
    IntrinsicGeneralizedRicciEquation D ↔
      ∀ b, ∀ c : MetricLeviCivitaFamily (cover.metric b).metric,
        OrdinaryMetricRicciPDE (cover.metric b).metric c (cover.interval b)
  ordinary_product : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval),
    RiemannianMetric.IsSmoothFamilyOn g I.domain →
      Nonempty (OrdinaryProductRicciGeometry g I)

end PoincareMT
