import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}

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

end PoincareConjecture.M14
