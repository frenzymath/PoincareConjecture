import PoincareConjecture.Definitions.M12HorizontalCalculus
import PoincareConjecture.Definitions.M12MovingGauge
import PoincareConjecture.Definitions.M12GaugeCover










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

section Ordinary

variable {n : ℕ} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]


abbrev MetricLeviCivitaFamily (g : ℝ → RiemannianMetric n C) :=
  (t : ℝ) → LeviCivitaData (g t)


def OrdinaryMetricRicciPDE (g : ℝ → RiemannianMetric n C)
    (D : MetricLeviCivitaFamily g) (I : SpacetimeInterval) : Prop :=
  ∀ t ∈ I.domain, ∀ x : C, ∀ u v : TangentSpace (𝓡 n) x,
    HasDerivWithinAt (fun s ↦ (g s).inner x u v)
      (-2 * (D t).ricci x u v) I.domain t


noncomputable def ordinaryMetricLieDerivative (g : RiemannianMetric n C)
    (D : LeviCivitaData g) (V : (x : C) → TangentSpace (𝓡 n) x)
    (x : C) (u v : TangentSpace (𝓡 n) x) : ℝ :=
  g.inner x (D.connection V x u) v + g.inner x u (D.connection V x v)

end Ordinary

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}


def IntrinsicGeneralizedRicciEquationOn (D : LeafwiseLeviCivitaFamily F S)
    (U : Set F.Point) : Prop :=
  ∀ p ∈ U, ∀ u v : F.Horizontal p,
    horizontalMetricLieDerivative F p u v = -2 * horizontalRicci D p u v


structure IntrinsicRicciFlow (F : GeneralizedFlowSpacetime n X time I)
    (S : ∀ t : ℝ, SpacetimeSliceGeometry F t) where
  leafwiseConnection : LeafwiseLeviCivitaFamily F S
  equation : IntrinsicGeneralizedRicciEquation leafwiseConnection

variable {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]


def MovingGaugeRicciPDE {e : MovingSpacetimeGauge F T C}
    (G : MovingSpacetimeGaugeGeometry e) (D : MetricLeviCivitaFamily G.metric) : Prop :=
  ∀ t (ht : t ∈ K.domain), ∀ x : C, ∀ u v : TangentSpace (𝓡 n) x,
    HasDerivWithinAt (fun s ↦ (G.metric s).inner x u v)
      (-2 * (D t).ricci x u v - ordinaryMetricLieDerivative (G.metric t) (D t)
        (movingGaugeDrift G ⟨t, ht⟩) x u v) K.domain t



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

end PoincareConjecture
