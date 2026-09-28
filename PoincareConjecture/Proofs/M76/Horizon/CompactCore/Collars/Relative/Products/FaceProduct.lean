import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Polygons.TriangleFibers



set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

structure SurfaceFaceProduct (T : CoorientedSurfaceStars E)
    (s : Finset E) where
  map : E × ℝ → E
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I)
  injective : InjOn map ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I)
  image_eq : map '' ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I) = T.dualRegion s
  central : ∀ x ∈ T.dualRegion s ∩ (T.marked 2).space, map (x, 0) = x
  proper : ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  rim : ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ T.dualRegionRim s ↔ x.1 ∈ T.dualRegionRim s ∩ (T.marked 2).space ∨
      x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ p : (T.marked 2).vertices, (p : E) ∈ s →
    ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
      0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ p : (T.marked 2).vertices, (p : E) ∈ s →
    ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
      T.height p (map x) ≤ 0 ↔ x.2 ≤ 0

end Geometry.SimplicialComplex

