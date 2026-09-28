import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskLowerProducts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexProducts









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}
  {C : HamiltonProperDiskCoherentSides T c}




structure HamiltonProperDiskVertexBand
    (P : HamiltonProperDiskLowerProducts T C) (p : T.disk.vertices) where

  map : E × ℝ → E

  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)

  injective : InjOn map ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)

  inside : MapsTo map ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)
    (T.dualRegionRim {(p : E)})

  central : ∀ x ∈ T.dualRegionRim {(p : E)} ∩ D, map (x, 0) = x

  positive : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    0 ≤ C.labels.height p (map x) ↔ 0 ≤ x.2

  negative : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    C.labels.height p (map x) ≤ 0 ↔ x.2 ≤ 0

  proper : ∀ x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I,
    map x ∈ frontier R ↔ x.1 ∈ frontier R

  keep_face : ∀ s ∈ T.disk.faces, 2 ≤ s.card → (p : E) ∈ s →
    ∀ x ∈ T.diskDualBase s ×ˢ I, map x = P.map s x

  frontier_image_subset : (T.vertexBlock p).space ∩ frontier R ⊆
    map '' ((T.dualRegionRim {(p : E)} ∩ D) ×ˢ I)

end PoincareConjecture.M76.HamiltonIndexOne
