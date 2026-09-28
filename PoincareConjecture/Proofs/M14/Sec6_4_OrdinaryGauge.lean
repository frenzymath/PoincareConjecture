import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import PoincareConjecture.Statements.M12GaugeTheory










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)




theorem ordinaryGaugeWitness_nonempty
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals) :
    Nonempty (OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)) := by
  apply hCoordinates.compatible_ordinary (G.gaugeCover.spatial b)
    (G.gaugeCover.interval b) (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)
  exact fun q _ => G.ricciEquation q




def ordinaryGaugeGeometry
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)) :
    MovingSpacetimeGaugeGeometry (G.gaugeCover.cylinder b).toMovingSpacetimeGauge where
  metric := W.flow.metric
  smooth := by
    rw [W.metric_eq]
    exact (G.gaugeCover.metric b).smooth
  spatialTangentEquiv := (G.gaugeCover.metric b).spatialTangentEquiv
  spatialTangentEquiv_eq := (G.gaugeCover.metric b).spatialTangentEquiv_eq
  metric_eq := W.metric_pullback




theorem ordinaryGauge_movingCalculus
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)) :
    MovingGaugeCalculus G.leafwise (ordinaryGaugeGeometry b W) W.flow.connection :=
  hCoordinates.moving_calculus (G.gaugeCover.spatial b) (G.gaugeCover.interval b)
    (G.gaugeCover.cylinder b).toMovingSpacetimeGauge (ordinaryGaugeGeometry b W) W.flow.connection



theorem ordinaryGauge_zero_drift
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x : G.gaugeCover.spatial b) :
    movingGaugeDrift (ordinaryGaugeGeometry b W) t x = 0 :=
  hCoordinates.compatible_zero_drift (G.gaugeCover.spatial b) (G.gaugeCover.interval b)
    (G.gaugeCover.cylinder b) (G.gaugeCover.metric b) t x

end PoincareConjecture.M14
