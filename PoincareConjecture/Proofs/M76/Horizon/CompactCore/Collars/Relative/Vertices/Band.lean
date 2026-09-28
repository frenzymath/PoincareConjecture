import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.LowerProducts
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.Blocks

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

variable {T : CoorientedSurfaceStars E}

local notation "I" => Icc (-1 : ℝ) 1

structure SurfaceVertexBand (P : SurfaceLowerProducts T)
    (p : (T.marked 2).vertices) where
  map : E × ℝ → E
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I)
  injective : InjOn map
    ((T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I)
  inside : MapsTo map
    ((T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I)
    (T.dualRegionRim {(p : E)})
  central : ∀ x ∈ T.dualRegionRim {(p : E)} ∩ (T.marked 2).space,
    map (x, 0) = x
  positive : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I,
    0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I,
    T.height p (map x) ≤ 0 ↔ x.2 ≤ 0
  proper : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  keep_face : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → (p : E) ∈ s →
    ∀ x ∈ T.surfaceBase s ×ˢ I, map x = P.map s x
  frontier_image_subset : (T.vertexBlock p).space ∩ (T.marked 1).space ⊆
    map '' ((T.dualRegionRim {(p : E)} ∩ (T.marked 2).space) ×ˢ I)

end Geometry.SimplicialComplex
