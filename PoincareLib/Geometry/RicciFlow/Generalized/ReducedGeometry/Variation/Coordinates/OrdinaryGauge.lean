import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Basic
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Theory

/-!
# Ordinary Ricci-flow calculus in the actual compatible gauge

Morgan-Tian Definition 3.38 and Proposition 6.33, pp. 61, 120-121.
M12 supplies an ordinary flow on each compatible cylinder. Its metric
representative and connection can be used in the moving-gauge calculus
while retaining the cylinder's actual spatial tangent equivalence.
-/

set_option autoImplicit false
-- The cylinder and its moving-gauge presentation have the same tangent fibers.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)

/-- M12 supplies an ordinary Ricci flow for the actual compatible
cylinder because the intrinsic equation holds on its range,
Definition 3.38, p. 61. -/
theorem ordinaryGaugeWitness_nonempty
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals) :
    Nonempty (OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)) := by
  apply hCoordinates.compatible_ordinary (G.gaugeCover.spatial b)
    (G.gaugeCover.interval b) (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)
  exact fun q _ => G.ricciEquation q

/-- Present the same cylinder geometry using the ordinary witness's
equal metric representative and the original spatial tangent map,
Definition 3.38 and Proposition 6.33, pp. 61, 120-121. -/
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

/-- The witness's actual ordinary connection has all M12 moving-gauge
transport identities for the original spatial tangent identification,
Definition 3.38 and Proposition 6.33, pp. 61, 120-121. -/
theorem ordinaryGauge_movingCalculus
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b)) :
    MovingGaugeCalculus G.leafwise (ordinaryGaugeGeometry b W) W.flow.connection :=
  hCoordinates.moving_calculus (G.gaugeCover.spatial b) (G.gaugeCover.interval b)
    (G.gaugeCover.cylinder b).toMovingSpacetimeGauge (ordinaryGaugeGeometry b W) W.flow.connection

/-- Presenting the equal ordinary metric preserves the actual zero
drift of the compatible cylinder, Definition 3.38, p. 61. -/
theorem ordinaryGauge_zero_drift
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise
      (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x : G.gaugeCover.spatial b) :
    movingGaugeDrift (ordinaryGaugeGeometry b W) t x = 0 :=
  hCoordinates.compatible_zero_drift (G.gaugeCover.spatial b) (G.gaugeCover.interval b)
    (G.gaugeCover.cylinder b) (G.gaugeCover.metric b) t x

end PoincareMT.M14
