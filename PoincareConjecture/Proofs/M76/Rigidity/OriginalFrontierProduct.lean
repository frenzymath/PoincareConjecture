import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerProducts









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



structure OriginalFrontierProduct (P : OriginalLowerProducts T)
    (p : (T.marked 2).vertices) where
  map : (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3)
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I)
  injective : InjOn map
    ((T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I)
  image_eq : map ''
      ((T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I) =
    (T.vertexBlock p).space ∩ (T.marked 1).space
  central : ∀ x ∈ T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space,
    map (x, 0) = x
  rim : ∀ x ∈ (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I,
    map x ∈ ((T.vertexBlock p).link p).space ↔
      x.1 ∈ ((T.vertexBlock p).link p).space ∨ x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ x ∈ (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I,
    0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ x ∈ (T.diskDualBase {(p : T.index → ℝ × V3)} ∩ (T.marked 1).space) ×ˢ I,
    T.height p (map x) ≤ 0 ↔ x.2 ≤ 0
  keep_edge : ∀ s ∈ (T.marked 2).faces, s ∈ (T.marked 1).faces →
    (p : T.index → ℝ × V3) ∈ s → s.card = 2 → ∀ t ∈ I,
      map (s.centroid ℝ id, t) = P.map s (s.centroid ℝ id, t)

end PoincareConjecture.M76
