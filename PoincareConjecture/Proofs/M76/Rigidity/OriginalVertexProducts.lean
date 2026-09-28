import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProducts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

open Classical in



structure OriginalVertexProducts (T : OriginalProperDiskTriangulation e R j) where
  map : (T.marked 2).vertices → (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3)
  piecewiseAffine : ∀ p : (T.marked 2).vertices,
    FinitePiecewiseAffineOn (map p) (T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I)
  injective : ∀ p : (T.marked 2).vertices,
    InjOn (map p) (T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I)
  image_eq : ∀ p : (T.marked 2).vertices,
    map p '' (T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I) =
      T.dualRegion {(p : T.index → ℝ × V3)}
  central : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.diskDualBase {(p : T.index → ℝ × V3)} → map p (x, 0) = x
  proper : ∀ (p : (T.marked 2).vertices) x,
    x ∈ T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I →
    (map p x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space)
  agrees : ∀ (p q : (T.marked 2).vertices) x,
    x ∈ (T.diskDualBase {(p : T.index → ℝ × V3)} ∩
      T.diskDualBase {(q : T.index → ℝ × V3)}) ×ˢ I → map p x = map q x
  overlap_image : ∀ p q : (T.marked 2).vertices,
    map p '' ((T.diskDualBase {(p : T.index → ℝ × V3)} ∩
      T.diskDualBase {(q : T.index → ℝ × V3)}) ×ˢ I) =
        T.dualRegion {(p : T.index → ℝ × V3)} ∩ T.dualRegion {(q : T.index → ℝ × V3)}

end PoincareConjecture.M76
