import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Polygons.TriangleProducts

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

structure SurfaceLowerProducts (T : CoorientedSurfaceStars E) where
  map : Finset E → E × ℝ → E
  piecewiseAffine : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    FinitePiecewiseAffineOn (map s) (T.surfaceBase s ×ˢ I)
  injective : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → InjOn (map s) (T.surfaceBase s ×ˢ I)
  image_eq : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    map s '' (T.surfaceBase s ×ˢ I) = T.dualRegion s
  central : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ x ∈ T.surfaceBase s, map s (x, 0) = x
  proper : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → ∀ x ∈ T.surfaceBase s ×ˢ I,
    map s x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  rim : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → ∀ x ∈ T.surfaceBase s ×ˢ I,
    map s x ∈ T.dualRegionRim s ↔
      x.1 ∈ T.dualRegionRim s ∩ (T.marked 2).space ∨ x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ p : (T.marked 2).vertices, (p : E) ∈ s →
      ∀ x ∈ T.surfaceBase s ×ˢ I, 0 ≤ T.height p (map s x) ↔ 0 ≤ x.2
  negative : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ p : (T.marked 2).vertices, (p : E) ∈ s →
      ∀ x ∈ T.surfaceBase s ×ˢ I, T.height p (map s x) ≤ 0 ↔ x.2 ≤ 0
  restrict : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, s ⊆ t → ∀ x ∈ T.surfaceBase t ×ˢ I, map s x = map t x
  agrees : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, 2 ≤ t.card →
      ∀ x ∈ (T.surfaceBase s ∩ T.surfaceBase t) ×ˢ I, map s x = map t x
  overlap_image : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, 2 ≤ t.card →
      map s '' ((T.surfaceBase s ∩ T.surfaceBase t) ×ˢ I) =
        T.dualRegion s ∩ T.dualRegion t
  boundary_image : ∀ s ∈ (T.marked 2).faces, s.card = 2 → s ∈ (T.marked 1).faces →
    (fun r : ℝ => map s (s.centroid ℝ id, r)) '' I =
      T.dualRegion s ∩ (T.marked 1).space

end Geometry.SimplicialComplex
