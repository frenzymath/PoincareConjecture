import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBlocks

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  {T : OriginalProperDiskTriangulation e R j}

open Classical in

structure OriginalVertexBand (P : OriginalLowerProducts T)
    (p : (T.marked 2).vertices) where
  map : (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3)
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I)
  injective : InjOn map
    ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I)
  inside : MapsTo map
    ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I)
    (T.dualRegionRim {(p : T.index → ℝ × V3)})
  central : ∀ x ∈ T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space,
    map (x, 0) = x
  positive : ∀ x ∈ (T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I,
    0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ x ∈ (T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I,
    T.height p (map x) ≤ 0 ↔ x.2 ≤ 0
  proper : ∀ x ∈ (T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  keep_face : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → (p : T.index → ℝ × V3) ∈ s →
    ∀ x ∈ T.diskDualBase s ×ˢ I, map x = P.map s x
  frontier_image_subset : (T.vertexBlock p).space ∩ (T.marked 1).space ⊆
    map '' ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I)

end PoincareConjecture.M76
