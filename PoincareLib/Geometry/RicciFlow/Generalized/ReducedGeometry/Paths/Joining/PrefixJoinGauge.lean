import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeLift

/-!
# Fixed gauge data for an interior prefix replacement

The curve approximation for Morgan-Tian Proposition 6.30, pp. 118-119,
uses one inverse gauge and one compact convex spatial region for all
sufficiently small transition widths. Both curve pieces have their
actual clocks and remain in the retained gauge image.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}

/-- One actual inverse gauge, time window and compact convex spatial
region containing a full curve and a competing prefix at their common
join, as used in Proposition 6.30, pp. 118-119. -/
structure PrefixJoinGauge (q : M14BackwardPath G T τ₁ τ₂ x y)
    (p : M14BackwardPath G T τ₁ c x (q.curve c)) where
  index : G.gaugeCover.index
  image : Set G.Point
  image_open : IsOpen image
  lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval index)).Point ×
    G.gaugeCover.spatial index
  lift_smooth : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift image
  lift_right : ∀ z ∈ image, (G.gaugeCover.cylinder index).toSpacetime (lift z) = z
  lift_time : ∀ z ∈ image, (lift z).1.val = G.spacetime.timeFunction z
  radius : ℝ
  radius_pos : 0 < radius
  left_margin : τ₁ < c - radius
  right_margin : c + radius < τ₂
  spatialRegion : Set (EuclideanSpace ℝ (Fin n))
  region_compact : IsCompact spatialRegion
  region_convex : Convex ℝ spatialRegion
  region_subset : spatialRegion ⊆ G.gaugeCover.spatial index
  image_coordinates : ∀ z ∈ image, (lift z).2.val ∈ spatialRegion
  prefix_in_image : ∀ s ∈ Icc (c - radius) c, p.curve s ∈ image
  continuation_in_image : ∀ s ∈ Icc (c - radius) (c + radius), q.curve s ∈ image

end PoincareMT.M14
