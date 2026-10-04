import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugePullback
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeCoefficients
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Manifold.OpenSubsetVelocity

/-!
# Actual covariant fields in ordinary gauge coordinates

Morgan-Tian Lemma 6.4 and Proposition 6.33, pp. 107-108, 120-121.
The actual clock supplies the ordinary coefficient's time membership.
The actual within spatial velocity and pulled-back field then give
M08's Christoffel-coordinate formula for every horizontal extension.
-/

set_option autoImplicit false
-- Product and open spatial tangent fibers use their actual model coordinates.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b} {J : Set ℝ}

private theorem gauge_within_spatialVelocity {s : ℝ}
    (hβ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s (1 : ℝ)).2 =
      derivWithin (fun r => (β r).2.val) J s := by
  have hd := congrArg (fun L => (L (1 : ℝ)).2)
    (mfderivWithin_prodMk hβ.fst hβ.snd hJ.uniqueMDiffWithinAt)
  change (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s (1 : ℝ)).2 =
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) (fun r => (β r).2) J s (1 : ℝ) at hd
  exact hd.trans ((G.gaugeCover.spatial b).mfderivWithin_curve_eq_derivWithin_val hβ.snd hJ)

/-- The ordinary coefficient at a selected square time gives the
actual horizontal derivative along any gauge curve through that time.
The curve parameter is independent of the coefficient parameter, as
needed for variation acceleration in Proposition 6.33, pp. 120-121. -/
theorem horizontalCovariantDerivative_gauge_coefficient
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (T : ℝ) (x : G.gaugeCover.spatial b) {C : Set ℝ}
    (htime : ∀ r ∈ C, T - r ^ 2 ∈ (G.gaugeCover.interval b).domain)
    {Y : ∀ r, G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β r))}
    (E : M14PullbackExtension G (fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)) J Y)
    {s σ : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s)
    (hβ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s)
    (hσ : σ ∈ C) (hclock : (β s).1.val = T - σ ^ 2) :
    (show EuclideanSpace ℝ (Fin n) from
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm
        (M14HorizontalCovariantDerivative G
          (fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)) J Y E s)) =
      derivWithin (fun r => (show EuclideanSpace ℝ (Fin n) from
        ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2).symm (Y r))) J s +
      M08.closedChartConnection W.flow T x C (σ, (β s).2.val)
        (derivWithin (fun r => (β r).2.val) J s)
        (((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm (Y s)) := by
  have h := horizontalCovariantDerivative_gauge_coordinates
    (G.gaugeCover.cylinder b).toMovingSpacetimeGauge (ordinaryGaugeGeometry b W)
    (ordinaryGauge_movingCalculus b hCoordinates W) (ordinaryGauge_zero_drift b hCoordinates W)
    E hs hJ hβ
  dsimp only [ordinaryGaugeGeometry] at h
  rw [hclock, openSubset_chartConnection (G.gaugeCover.spatial b) W.flow T htime x
    (β s).2 hσ, gauge_within_spatialVelocity b hβ hJ] at h
  exact h

/-- The actual horizontal derivative has the ordinary Christoffel
coordinate formula on the curve's own parameter set, including unique
within endpoints, Lemma 6.4 and Proposition 6.33, pp. 107-108, 120-121. -/
theorem horizontalCovariantDerivative_gauge_chart
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (T : ℝ) (x : G.gaugeCover.spatial b)
    (hclock : ∀ r ∈ J, (β r).1.val = T - r ^ 2)
    {Y : ∀ r, G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β r))}
    (E : M14PullbackExtension G (fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)) J Y)
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s)
    (hβ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s) :
    (show EuclideanSpace ℝ (Fin n) from
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm
        (M14HorizontalCovariantDerivative G
          (fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)) J Y E s)) =
      derivWithin (fun r => (show EuclideanSpace ℝ (Fin n) from
        ((G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2).symm (Y r))) J s +
      M08.closedChartConnection W.flow T x J (s, (β s).2.val)
        (derivWithin (fun r => (β r).2.val) J s)
        (((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm (Y s)) := by
  have htime (r : ℝ) (hr : r ∈ J) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr]
    exact (β r).1.property
  exact horizontalCovariantDerivative_gauge_coefficient b hCoordinates W T x htime
    E hs hJ hβ hs (hclock s hs)

end PoincareMT.M14
