import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleProducts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

noncomputable def OriginalProperDiskTriangulation.diskDualBase
    (T : OriginalProperDiskTriangulation e R j) (s : Finset (T.index → ℝ × V3)) :
    Set (T.index → ℝ × V3) := T.dualRegion s ∩ (T.marked 2).space

structure OriginalLowerProducts (T : OriginalProperDiskTriangulation e R j) where
  map : Finset (T.index → ℝ × V3) → (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3)
  piecewiseAffine : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    FinitePiecewiseAffineOn (map s) (T.diskDualBase s ×ˢ I)
  injective : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → InjOn (map s) (T.diskDualBase s ×ˢ I)
  image_eq : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    map s '' (T.diskDualBase s ×ˢ I) = T.dualRegion s
  central : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ x ∈ T.diskDualBase s, map s (x, 0) = x
  proper : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → ∀ x ∈ T.diskDualBase s ×ˢ I,
    map s x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  rim : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card → ∀ x ∈ T.diskDualBase s ×ˢ I,
    map s x ∈ T.dualRegionRim s ↔
      x.1 ∈ T.dualRegionRim s ∩ (T.marked 2).space ∨ x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s →
      ∀ x ∈ T.diskDualBase s ×ˢ I, 0 ≤ T.height p (map s x) ↔ 0 ≤ x.2
  negative : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s →
      ∀ x ∈ T.diskDualBase s ×ˢ I, T.height p (map s x) ≤ 0 ↔ x.2 ≤ 0
  restrict : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, s ⊆ t → ∀ x ∈ T.diskDualBase t ×ˢ I, map s x = map t x
  agrees : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, 2 ≤ t.card →
      ∀ x ∈ (T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I, map s x = map t x
  overlap_image : ∀ s ∈ (T.marked 2).faces, 2 ≤ s.card →
    ∀ t ∈ (T.marked 2).faces, 2 ≤ t.card →
      map s '' ((T.diskDualBase s ∩ T.diskDualBase t) ×ˢ I) =
        T.dualRegion s ∩ T.dualRegion t
  boundary_image : ∀ s ∈ (T.marked 2).faces, s.card = 2 → s ∈ (T.marked 1).faces →
    (fun r : ℝ => map s (s.centroid ℝ id, r)) '' I =
      T.dualRegion s ∩ (T.marked 1).space

end PoincareConjecture.M76
