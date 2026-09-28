import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.LowerProducts

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

structure SurfaceVertexProducts (T : CoorientedSurfaceStars E) where
  map : (T.marked 2).vertices → E × ℝ → E
  piecewiseAffine : ∀ p : (T.marked 2).vertices,
    FinitePiecewiseAffineOn (map p) (T.surfaceBase {(p : E)} ×ˢ I)
  injective : ∀ p : (T.marked 2).vertices,
    InjOn (map p) (T.surfaceBase {(p : E)} ×ˢ I)
  image_eq : ∀ p : (T.marked 2).vertices,
    map p '' (T.surfaceBase {(p : E)} ×ˢ I) =
      T.dualRegion {(p : E)}
  central : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.surfaceBase {(p : E)} → map p (x, 0) = x
  proper : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.surfaceBase {(p : E)} ×ˢ I →
    (map p x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space)
  positive : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.surfaceBase {(p : E)} ×ˢ I →
    (0 ≤ T.height p (map p x) ↔ 0 ≤ x.2)
  negative : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.surfaceBase {(p : E)} ×ˢ I →
    (T.height p (map p x) ≤ 0 ↔ x.2 ≤ 0)
  agrees : ∀ (p q : (T.marked 2).vertices) x,
    x ∈ (T.surfaceBase {(p : E)} ∩
      T.surfaceBase {(q : E)}) ×ˢ I → map p x = map q x
  overlap_image : ∀ p q : (T.marked 2).vertices,
    map p '' ((T.surfaceBase {(p : E)} ∩
      T.surfaceBase {(q : E)}) ×ˢ I) =
        T.dualRegion {(p : E)} ∩ T.dualRegion {(q : E)}

end Geometry.SimplicialComplex
