import PoincareConjecture.Statements.M12MetricPredecessors
import PoincareConjecture.Statements.M12HorizontalTheory
import PoincareConjecture.Statements.M12GaugeTheory










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture



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

end PoincareConjecture
