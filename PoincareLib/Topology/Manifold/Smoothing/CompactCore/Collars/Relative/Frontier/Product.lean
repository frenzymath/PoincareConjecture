import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.Relative.Products.LowerProducts
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.Relative.Vertices.Blocks

/-! # Complete frontier vertex geometry in a cooriented surface model -/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {T : CoorientedSurfaceStars E}

open Classical in
/-- One full original frontier product preserving the already chosen
incident boundary-edge products. Its producer assumes no frontier
product or extra side data. See rigidity030. -/
structure SurfaceFrontierProduct (P : SurfaceLowerProducts T)
    (p : (T.marked 2).vertices) where
  map : (E) × ℝ → (E)
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I)
  injective : InjOn map
    ((T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I)
  image_eq : map ''
      ((T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I) =
    (T.vertexBlock p).space ∩ (T.marked 1).space
  central : ∀ x ∈ T.surfaceBase {(p : E)} ∩ (T.marked 1).space,
    map (x, 0) = x
  rim : ∀ x ∈ (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I,
    map x ∈ ((T.vertexBlock p).link p).space ↔
      x.1 ∈ ((T.vertexBlock p).link p).space ∨ x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ x ∈ (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I,
    0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ x ∈ (T.surfaceBase {(p : E)} ∩ (T.marked 1).space) ×ˢ I,
    T.height p (map x) ≤ 0 ↔ x.2 ≤ 0
  keep_edge : ∀ s ∈ (T.marked 2).faces, s ∈ (T.marked 1).faces →
    (p : E) ∈ s → s.card = 2 → ∀ t ∈ I,
      map (s.centroid ℝ id, t) = P.map s (s.centroid ℝ id, t)

end Geometry.SimplicialComplex

